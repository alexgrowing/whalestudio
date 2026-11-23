import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBasis

theorem exists_sec_of_ker {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {M : LB Y} (P : Perf f M) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0) :
    ∃ s : LB.Sec M, ∀ i, rs Y (P.le i) (s.f (P.ch i)) = Seesaw.loc₀ P v i := by
  have h : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) Y (𝟙 Y) f h
  let t := E ⟨v, hv⟩
  have le : ∀ j, M.U j ≤ (M.pull (𝟙 Y)).U (fun _ => j) := fun j => le_pull M (𝟙 Y) le_rfl
  refine ⟨⟨fun j => rs Y (le j) (t.f fun _ => j), fun i j => ?_⟩, fun i => ?_⟩
  · have e := GlobalTheory.LB.sec_rel t (fun _ => i) (fun _ => j) (inf_le_left.trans (le i))
      (inf_le_right.trans (le j)) (inf_le_inf (le i) (le j))
    have e' := (GlobalTheory.LB.resG_pull_g (L := M) (𝟙 Y) (fun _ => i) (fun _ => j)
      (inf_le_inf (le i) (le j))).trans (rs_self _ _)
    exact (rs_rs _ _ _).trans (e.trans (congrArg₂ (· * ·) e' (rs_rs _ _ _).symm))
  · exact (rs_rs _ _ _).trans (hE ⟨v, hv⟩ i)

theorem exists_sec_iso {X X' : Scheme.{0}} {β : X' ⟶ X} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB)
    (w : LB.Iso M' (M.pull β)) (hw : w.IsGen) (s : LB.Sec M') :
    ∃ t : LB.Sec (M.pull β), ∀ z k k', β z ∈ M.U k → z ∈ M'.U k' →
      gs (𝟙 X') z _ (t.f fun _ => k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 X') z _ (s.f k') := by
  refine ⟨SecOn.topEquiv _ (SecOn.congr hM' (LB.isLB_pull hM β) w hw ⊤ ((SecOn.topEquiv M').symm s)),
    fun z k k' hk hk' => ?_⟩
  have hz : z ∈ (M.pull β).U (fun _ => k) ⊓ M'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (gs (𝟙 X') z _) (SecOn.coord_congr hM' (LB.isLB_pull hM β) w hw
    ((SecOn.topEquiv M').symm s) (fun _ => k) k' (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl)
  rw [gs_mul _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz] at e
  refine (gs_res _ _ _ hz.1 _).trans (e.trans (congrArg₂ (· * ·) (gs_unit _ _ _ hz _) ?_))
  exact gs_res (𝟙 X') z (inf_le_right : ⊤ ⊓ M'.U k' ≤ _) ⟨trivial, hk'⟩ (s.f k')

theorem gs_comb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (z : X)
    {U : X.Opens} (h : z ∈ U) {n : ℕ} (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs (𝟙 X) z U (∑ j, AbLaw.cst f U (c j) * x j) = ∑ j, gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ (c j)) * gs (𝟙 X) z U (x j) := by
  rw [gs_eq _ _ _ h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← gs_eq _ _ _ h, gs_mul _ _ _ h, ← rs_cst f (le_top : U ≤ ⊤), gs_res _ _ _ h]

theorem loc_mulVec {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {n : ℕ} (B : Matrix (Fin P.a) (Fin n) R') (c : Fin n → R') (i : P.I) :
    Seesaw.loc P π f' (B.mulVec c) i = ∑ j, AbLaw.cst f' _ (c j) * Seesaw.loc P π f' (fun k => B k j) i := by
  simp only [Seesaw.loc, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem exists_basis : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, AbLaw.cst f' (M'.U k) (c i) * (τ' i).f k := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ h₀ M₀ w₀ hM₀ hw₀ hH
  obtain ⟨P⟩ := nonempty_perf_of_noetherian A X f hf hp M hM
  obtain ⟨w₁, hw₁⟩ := LBIso.symm (⟨w₀, hw₀⟩ : LBIso _ _)
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point A K g₀ _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g₀ X₀ π f₀ h₀ (H1Iso.firstCohomologyVanishes_of_iso_of_isGen hM₀.cover (LB.isLB_pull hM π) w₁ hw₁ hH))
  have hru : IsUnit r := by
    by_contra hn
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g₀ hg₀)
    exact hr ((RingHom.mem_ker).1 (this ▸ (show r ∈ IsLocalRing.maximalIdeal A from hn)))
  choose τ hτ using fun j => exists_sec_of_ker P (fun k => B k j) (funext fun l => congrFun₂ hB l j)
  refine ⟨n, τ, fun A' _ g X' β f' h M' w τ' hM' hw hτ' s' => ?_⟩
  obtain ⟨E, hE⟩ := P.sec A' g X' β f' h
  obtain ⟨t, ht⟩ := exists_sec_iso hM hM' w hw s'
  obtain ⟨v, rfl⟩ := E.surjective t
  have hA : ∀ z i k', β z ∈ P.W i → z ∈ M'.U k' → gs (𝟙 X') z _ (Seesaw.loc P β f' v.1 i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val * gs (𝟙 X') z _ (s'.f k') := fun z i k' hi hk' =>
    (congrArg (gs (𝟙 X') z _) (hE v i).symm).trans ((gs_res (𝟙 X') z (le_pull M β (P.le i)) hi _).trans (ht z _ k' (P.le i hi) hk'))
  have hC : ∀ (c : Fin n → A') z i k', β z ∈ P.W i → z ∈ M'.U k' →
      gs (𝟙 X') z _ (Seesaw.loc P β f' ((B.map g).mulVec c) i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val *
        gs (𝟙 X') z _ (∑ j, AbLaw.cst f' (M'.U k') (c j) * (τ' j).f k') := fun c z i k' hi hk' => by
    rw [loc_mulVec, gs_comb f' z (show z ∈ β ⁻¹ᵁ P.W i from hi), gs_comb f' z hk', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← hτ' j z _ k' (P.le i hi) hk']
    refine congrArg (_ * ·) ?_
    refine (congrArg (gs (𝟙 X') z _) (Seesaw.loc_comp P h (fun k => B k j) i)).trans ?_
    rw [← hτ j i]
    refine (gs_pull (𝟙 X') β z _ hi _).trans ?_
    rw [Category.id_comp]
    exact gs_res β z _ hi _
  refine (existsUnique_congr fun c => ⟨fun hc k' => fn_ext fun z hz => ?_, fun hc => ?_⟩).1
    (hu A' g (hru.map g) v.1 v.2)
  · obtain ⟨i, hi⟩ := Seesaw.exists_mem P (β z)
    have e := hC c z i k' hi hz
    rw [hc, hA z i k' hi hz] at e
    exact (Units.mul_right_inj _).1 e
  · have hk : (P.D₀.map g).mulVec ((B.map g).mulVec c) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero g), Matrix.zero_mulVec]
    refine congrArg Subtype.val (E.injective (a₁ := ⟨_, hk⟩) (a₂ := v) ?_)
    refine Seesaw.sec_ext _ _ (fun i => β ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M β (P.le i))
      (fun y => Seesaw.exists_mem P (β y)) fun i => ?_
    refine (hE ⟨_, hk⟩ i).trans (Eq.trans (fn_ext fun z hz => ?_) (hE v i).symm)
    obtain ⟨k', hk'⟩ := exists_chart hM' z
    exact (hC c z i k' hz hk').trans ((congrArg (fun x => _ * gs (𝟙 X') z _ x) (hc k').symm).trans
      (hA z i k' hz hk').symm)

end GlobalTheory.SecBasis
