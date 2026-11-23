import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversally
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LinearMapCompEqOnSmulOfEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAlgClosedTransversal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyGeneric

section Sec

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem gs_pow' {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem via_iff_stalk (w : LB.Iso L' (L.pull F)) (l : ℕ) (a' : ∀ i, Γ(X', L'.U i)) (a : ∀ j, Γ(X, L.U j)) :
    GlobalTheory.KeyVia.Via w l a' a ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (a j) = (gw w r z j k).val ^ l * gs r z _ (a' k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy, gs_pow' _ z _ hy]
    exact congrArg (· ^ l * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy, gs_pow' _ y _ hy]
    exact congrArg (· ^ l * _) (gs_unit _ y _ hy _).symm

end Sec

theorem keyVia_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {φ w φ'' w''} (h : KeyVia x' x f φ w)
    (h'' : KeyVia x'' x (f'.comp f) φ'' w'') :
    ∃ φ' w', KeyVia x'' x' f' φ' w' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x φ'' w'' s'' s → SecVia x'' x' φ' w' s'' s' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := h
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := h''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := GlobalTheory.KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', ⟨he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (GlobalTheory.KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' hs' hs'' => (via_iff_stalk w' l s''.f s'.f).2 fun Z q z i k hi hk => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (GlobalTheory.KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (GlobalTheory.KeyCancel.appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (via_iff_stalk w l s'.f s.f).1 hs' Z (q ≫ φ') z j i hj hi
    have b := (via_iff_stalk w'' l s''.f s.f).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, mul_pow, _root_.mul_assoc] at b
    exact ((Units.isUnit _).pow l).mul_left_cancel b

theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, GlobalTheory.AbLaw.cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i),
    fun i j => ?_⟩, fun i => rfl⟩
  refine (map_sum _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (map_sum _ _ _).symm))
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (Finset.mul_sum _ _ _).symm
  refine (map_mul _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (map_mul _ _ _).symm))
  refine (congrArg₂ (· * ·) ((rs_cst _ _ _).trans (rs_cst _ _ _).symm) ((b k).compat i j)).trans (mul_left_comm _ _ _)

theorem finZ_of_etZ {K : Type} [Field K] {x : KeyIn K} {n d : ℕ} {s : Fin x.P.g → RR x n} {z : Fin d → Pt x}
    {ch : Fin d → x.P.L.ι} (h : EtZ x s z ch) : FinZ x s := by
  haveI : Finite (Sp K) := inferInstanceAs (Finite (PrimeSpectrum K))
  refine (Set.finite_range fun q : Fin d × Sp K => (z q.1).left q.2).subset fun y hy => ?_
  obtain ⟨a, p, e⟩ := h.2.2.2.2 y hy
  exact ⟨(a, p), e⟩

theorem degProd_ne_zero {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (h : admitted g n l l' al) :
    degProd g n l l' ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hj' : j * n ≤ g * n := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  obtain ⟨-, h₁, h₂, -⟩ := h
  exact mul_ne_zero (by omega) (by omega)

theorem exists_field {k K I I' : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] {U : I → K} {V : I' → K}
    (h : AlgebraicIndependent k (Sum.elim V U)) :
    ∃ (E : IntermediateField k K) (U' : I → E), IsAlgClosed E ∧ (∀ i, (U' i : K) = U i) ∧
      AlgebraicIndependent k U' ∧ AlgebraicIndependent E V := by
  obtain ⟨h₁, h₂⟩ := AlgebraicIndependent.sumElim_iff.1 h
  have h₃ := IntermediateField.algebraicIndependent_adjoin_iff.2 h₂
  let A := IntermediateField.adjoin k (Set.range U)
  have h₄ : AlgebraicIndependent (algebraicClosure A K) V := h₃.algebraicClosure
  refine ⟨(algebraicClosure A K).restrictScalars k, fun i => ⟨U i, ?_⟩, (algebraicClosure.isAlgClosure A K).isAlgClosed,
    fun _ => rfl, ?_, h₄⟩
  · exact (algebraicClosure A K).algebraMap_mem ⟨U i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  · exact AlgebraicIndependent.of_comp (IntermediateField.val _) h₁

theorem secVia_of_coords {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (h : KeyVia x' x f φ w) {l N : ℕ} {b : Fin N → RR x l} {b' : Fin N → RR x' l} (hb : ∀ j, SecVia x' x φ w (b' j) (b j))
    {c : Fin N → R} {s : RR x l} {s' : RR x' l} (hs : Coords x b c s.f) (hs' : Coords x' b' (fun j => f (c j)) s'.f) :
    SecVia x' x φ w s' s := by
  obtain ⟨σ, hσ, -⟩ := ((GlobalTheory.KeyVia.main R R' x x' f).2 φ w h).1 l s
  have e := ((GlobalTheory.KeyVia.main R R' x x' f).2 φ w h).2.2 l N b b' s σ c hb hσ hs
  have e' : σ.f = s'.f := funext fun i => (e i).trans (hs' i).symm
  obtain ⟨tf, _⟩ := σ
  obtain ⟨sf, _⟩ := s'
  obtain rfl : tf = sf := e'
  exact hσ

theorem finZ_of_generic (hL : Out.Laws) {k K : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] {x : KeyIn k}
    {x' : KeyIn K} {φ w} {n G : ℕ} (hG : x'.P.g = G) {b : Fin (n ^ x.P.g) → RR x n} {b' : Fin (n ^ x.P.g) → RR x' n}
    {T : Fin G × Fin (n ^ x.P.g) → K} {s : Fin G → RR x' n} (hn : 4 ≤ n) (h : KeyVia x' x (algebraMap k K) φ w)
    (hb : IsBasis x b) (hb' : ∀ j, SecVia x' x φ w (b' j) (b j)) (hT : AlgebraicIndependent k T)
    (hs : ∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) : FinZ x' s := by
  subst hG
  obtain ⟨d, z, ch, H⟩ := GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent hL k K x x' φ w n b b' T s hn h hb hb' hT hs
  exact finZ_of_etZ H

theorem finZ_line (hL : Out.Laws) {k K : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] {x : KeyIn k}
    {x' : KeyIn K} {φ w} {n : ℕ} {b : Fin (n ^ x.P.g) → RR x n} {b' : Fin (n ^ x.P.g) → RR x' n}
    {U : Fin x'.P.g × Fin (n ^ x.P.g) → K} {V : Fin (n ^ x.P.g) → K} {s σ : Fin x'.P.g → RR x' n} {s₁ : RR x' n}
    (hn : 4 ≤ n) (h : KeyVia x' x (algebraMap k K) φ w) (hb : IsBasis x b) (hb' : ∀ j, SecVia x' x φ w (b' j) (b j))
    (hT : AlgebraicIndependent k (Sum.elim V U)) (hs : ∀ i, Coords x' b' (fun j => U (i, j)) (s i).f)
    (hs₁ : Coords x' b' V s₁.f) (i₀ : Fin x'.P.g) (t : K) (hσ : ∀ i, i ≠ i₀ → (σ i).f = (s i).f)
    (hσ₀ : ∀ c, (show Γ(x'.P.A.left, x'.P.L.U c) from (σ i₀).f c) =
      GlobalTheory.AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from (s i₀).f c) +
        GlobalTheory.AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from s₁.f c)) : FinZ x' σ := by
  obtain ⟨E, U', hE, hU', hUi, hVi⟩ := exists_field hT
  obtain ⟨y, hy⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange k E x (algebraMap k E)
  obtain ⟨φ₁, w₁, h₁⟩ := (GlobalTheory.KeyVia.main k E x y _).1.1 hy
  have h' : KeyVia x' x ((algebraMap E K).comp (algebraMap k E)) φ w := by
    rw [← IsScalarTower.algebraMap_eq]; exact h
  obtain ⟨φ₂, w₂, h₂, hc⟩ := keyVia_cancel h₁ h'
  choose b₁ hb₁ using fun j => (((GlobalTheory.KeyVia.main k E x y _).2 φ₁ w₁ h₁).1 n (b j)).exists
  have hb₂ : ∀ j, SecVia x' y φ₂ w₂ (b' j) (b₁ j) := fun j => hc n _ _ _ (hb₁ j) (hb' j)
  have hB : IsBasis y b₁ := (GlobalTheory.KeyBasis.main hL k x n (by omega)).2 b hb E _ y φ₁ w₁ b₁ h₁ hb₁
  choose r hr using fun i : Fin x'.P.g => exists_coords y b₁ fun j => U' (i, j)
  have hg₁ : y.P.g = x.P.g := h₁.2.1
  have hg₂ : x'.P.g = y.P.g := h₂.2.1
  have hfin : FinZ y r := finZ_of_generic hL hg₂.symm hn h₁ hb hb₁ hUi hr
  have hrs : ∀ i, SecVia x' y φ₂ w₂ (s i) (r i) := fun i => secVia_of_coords h₂ hb₂ (hr i) <| by
    have e : (fun j => algebraMap E K (U' (i, j))) = fun j => U (i, j) := funext fun j => hU' _
    rw [e]; exact hs i
  have key : ∀ (N : ℕ) (_ : n ^ y.P.g = N) (b₁ : Fin N → RR y n) (b' : Fin N → RR x' n) (V : Fin N → K),
      IsBasis y b₁ → (∀ j, SecVia x' y φ₂ w₂ (b' j) (b₁ j)) → AlgebraicIndependent E V → Coords x' b' V s₁.f →
      FinZ x' σ := by
    rintro N rfl b₁ b' V hB hb₂ hVi hs₁
    refine GlobalTheory.KeyKa.finZ_of_line_towards_generic hL E K y x' φ₂ w₂ n b₁ b' _ r σ i₀ (s i₀) s₁ V t hn h₂ hB hb₂ hfin hVi (fun i hi => ?_) (hrs i₀)
      hs₁ hσ₀
    have e := hσ i hi
    intro j a hh
    rw [e]
    exact hrs i j a hh
  exact key _ (by rw [hg₁]) b₁ b' V hB hb₂ hVi hs₁

theorem kaVal_eq_of_generic : Out.Laws → ∀ (k K : Type) [Field k] [CharZero k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T T' : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s s' : Fin x'.P.g → RR x' n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k (Sum.elim T T') → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → (∀ i, Coords x' b' (fun j => T' (i, j)) (s' i).f) → KaVal x' n l l' al s κ → KaVal x' n l l' al s' κ' → κ = κ' := by
  intro hL k K _ _ _ _ _ x x' φ w n l l' al b b' T T' s s' κ κ' hA h hb hb' hT hs hs' hκ hκ'
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have hg : x'.P.g = x.P.g := h.2.1
  have hA' : admitted x'.P.g n l l' al := by rw [hg]; exact hA
  have hn : 4 ≤ n := hA.1
  let sl : Finset (Fin x'.P.g) → Fin x'.P.g × Fin (n ^ x.P.g) →
      (Fin x'.P.g × Fin (n ^ x.P.g)) ⊕ (Fin x'.P.g × Fin (n ^ x.P.g)) :=
    fun S p => if p.1 ∈ S then Sum.inr p else Sum.inl p
  have hsl : ∀ S p, Sum.elim id id (sl S p) = p := fun S p => by
    by_cases hp : p.1 ∈ S <;> simp [sl, hp]
  have hco : ∀ S i, Coords x' b' (fun j => Sum.elim T T' (sl S (i, j))) (S.piecewise s' s i).f := fun S i => by
    by_cases hp : i ∈ S
    · simpa [sl, hp] using hs' i
    · simpa [sl, hp] using hs i
  have main : ∀ (S : Finset (Fin x'.P.g)) (ρ : Kˣ), KaVal x' n l l' al (S.piecewise s' s) ρ → κ = ρ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro ρ hρ
      rw [Finset.piecewise_empty] at hρ
      refine GlobalTheory.KeyLine.kaVal_eq_of_line hL K x' n l l' al s s κ ρ hA' (fun t σ hσ => ?_) hκ hρ
      refine finZ_of_generic hL rfl hn h hb hb' (T := T) (hT.comp Sum.inl Sum.inl_injective) fun i c => ?_
      refine (hσ i c).trans (Eq.trans ?_ (hs i c))
      rw [← add_mul, ← map_add, sub_add_cancel, map_one, _root_.one_mul]
    | insert i₀ S hi ih =>
      intro ρ hρ
      have hinj : Function.Injective (sl S) := Function.LeftInverse.injective (hsl S)
      obtain ⟨d, z, ch, H⟩ := GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent hL k K x x' φ w n b b' (Sum.elim T T' ∘ sl S) _ hn h hb hb'
        (hT.comp _ hinj) (hco S)
      obtain ⟨ν, hν⟩ := GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed hL K x' n l l' al d _ z ch hA' (Nat.cast_ne_zero.2 (degProd_ne_zero hA')) H
      refine (ih ν hν).trans (GlobalTheory.KeyLine.kaVal_eq_of_line hL K x' n l l' al _ _ ν ρ hA' (fun t σ hσ => ?_) hν hρ)
      have hinj' : Function.Injective (Sum.elim (fun j => Sum.inr (i₀, j)) (sl S)) := by
        refine Function.Injective.sumElim (fun j j' e => by simpa using e) hinj fun j p e => ?_
        have e' : (i₀, j) = p := (congrArg (Sum.elim id id) e).trans (hsl S p)
        subst e'
        simp [sl, hi] at e
      have hT' : AlgebraicIndependent k (Sum.elim (fun j => T' (i₀, j)) (Sum.elim T T' ∘ sl S)) := by
        have := hT.comp _ hinj'
        rwa [Sum.comp_elim] at this
      refine finZ_line hL hn h hb hb' hT' (hco S) (hs' i₀) i₀ t (fun i hi' => funext fun c => (hσ i c).trans ?_)
        fun c => ?_
      · rw [Finset.piecewise_insert_of_ne _ _ _ hi', ← add_mul, ← map_add, sub_add_cancel, map_one, _root_.one_mul]
      · have := hσ i₀ c
        rwa [Finset.piecewise_insert_self] at this
  exact main Finset.univ κ' (by rwa [Finset.piecewise_univ])

end GlobalTheory.KeyGeneric
end
