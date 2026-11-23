import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmersedByOfLocalCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

namespace GlobalTheory.FlagPlucker.Sep

theorem initSpan_min {S N : Type} [CommRing S] [AddCommGroup N] [Module S N] {d : ℕ} (v : Fin d → N) (i : ℕ) :
    initSpan S v i = initSpan S v (min i d) := by
  unfold initSpan
  congr 2
  ext j
  simp only [Set.mem_setOf_eq, lt_min_iff, j.2, and_true]

theorem initSpan_cols_eq {K : Type} [Field K] {n d : ℕ} (P P' : Matrix (Fin n) (Fin d) K)
    (hP : LinearIndependent K (fun j r => P r j))
    (h : ∀ m : Fin d, ∃ u : Kˣ, ∀ r : Fin ((m : ℕ) + 1) → Fin n,
      (P'.submatrix r (Fin.castLE m.2)).det = u * (P.submatrix r (Fin.castLE m.2)).det)
    (i : ℕ) : initSpan K (fun j r => P' r j) i = initSpan K (fun j r => P r j) i := by
  rcases n with _ | N
  · exact Subsingleton.elim _ _
  rw [initSpan_min (fun j r => P' r j) i, initSpan_min (fun j r => P r j) i]
  rcases hmi : min i d with _ | m
  · unfold initSpan
    have e0 : {j : Fin d | (j : ℕ) < 0} = ∅ := Set.eq_empty_of_forall_notMem fun j hj => Nat.not_lt_zero _ hj
    rw [e0, Set.image_empty, Set.image_empty]
  have hm : m < d := by have := min_le_right i d; omega
  have hr : ∀ Q : Matrix (Fin (N + 1)) (Fin d) K, initSpan K (fun j r => Q r j) (m + 1) =
      Submodule.span K (Set.range fun l : Fin (m + 1) => (fun j r => Q r j) (Fin.castLE hm l)) := by
    intro Q
    unfold initSpan
    congr 1
    ext w
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨_, show ((Fin.castLE hm l : Fin d) : ℕ) < m + 1 from l.2, rfl⟩
  rw [hr, hr]
  obtain ⟨u, hu⟩ := h ⟨m, hm⟩
  have hind : LinearIndependent K fun l : Fin (m + 1) => (fun j r => P r j) (Fin.castLE hm l) :=
    hP.comp _ (Fin.castLE_injective _)
  refine (((GlobalTheory.FlagEmb.PlkSpan.main K N (m + 1) _ _).2 hind).2 ⟨u, ?_⟩).2
  funext q
  simp only [GlobalTheory.FlagEmb.plk, id, Pi.smul_apply, smul_eq_mul]
  have e : ∀ Q : Matrix (Fin (N + 1)) (Fin d) K, (Matrix.of fun l l' : Fin (m + 1) =>
      (fun j r => Q r j) (Fin.castLE hm l) (GlobalTheory.FlagEmb.plE N (m + 1) q l')) =
      (Q.submatrix (GlobalTheory.FlagEmb.plE N (m + 1) q) (Fin.castLE hm)).transpose := by
    intro Q; ext; rfl
  rw [e, e, Matrix.det_transpose, Matrix.det_transpose]
  exact hu _

end GlobalTheory.FlagPlucker.Sep

noncomputable section

namespace GlobalTheory.FlagPlucker.Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem initSpan_comp {S N N' : Type} [CommRing S] [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S N']
    {d : ℕ} (L : N →ₗ[S] N') (v : Fin d → N) (i : ℕ) : initSpan S (L ∘ v) i = (initSpan S v i).map L := by
  unfold initSpan
  rw [Submodule.map_span, Set.image_comp]

theorem vecAt_eq_vec (F : Frames Y π) (Mc : MChart Y) (k : F.J) {S : Type} [CommRing S] (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hM : ⊤ ≤ x ⁻¹ᵁ Mc.U)
    (hzU : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    F.vecAt k z hz hx σ j = vec Mc x hM (fun r => (plkU F Mc k σ).map (ev z _ hzU) r j) := by
  subst hx
  have hh : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (Mc.U ⊓ (F.M k).U) := le_preimage_inf hM (F.inM hz rfl)
  rw [Frames.vecAt, ← vec_chg Mc (F.M k).toMChart (z ≫ π) hM (F.inM hz rfl) hh]
  congr 1
  funext r
  rw [plkU, Matrix.map_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.map_apply]
  exact congrArg₂ (· * ·) (ev_appLE z π _ hzU hh _).symm (ev_res z _ hzU hz _).symm

theorem valF_plkLoc (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) {K : Type} [Field K] (a : Sp K ⟶ T) (k : F.J)
    (hj : ⊤ ≤ a ⁻¹ᵁ ((F.LL (ind σ m)).pull g).U (fun _ => k)) (hU : ⊤ ≤ (a ≫ g) ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U))
    (r : Fin ((m : ℕ) + 1) → Fin Mc.n) :
    valF a _ (plkLoc F Mc g hg σ m (Fin.succ (Fintype.equivFin _ r)) (fun _ => k)) =
      (((plkU F Mc k σ).map (ev (a ≫ g) _ hU)).submatrix r (Fin.castLE m.2)).det := by
  have e : plkIdx Mc m (Fin.succ (Fintype.equivFin _ r)) = some r := by simp [plkIdx]
  simp only [plkLoc, e]
  rw [valF, dif_pos hj]
  show ev a _ hj ((g.appLE _ _ _).hom _) = _
  rw [ev_appLE a g _ hj hU, plkMinor, RingHom.map_det]
  rfl

end GlobalTheory.FlagPlucker.Sep

end

theorem GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (t : ∀ (σ : E →+* ℂ) (m : Fin (Dw.mult σ)), Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ σ m q, (t σ m q).f = plkLoc F Mc g hg σ m q) → ∀ (ht : ∀ σ m, ⨆ q, nonzeroLocus (t σ m q) = ⊤) {R : Type} [CommRing R] (f : T ⟶ Sp R) (K : Type) [Field K] (a a' : Sp K ⟶ T), a ≫ g ≫ π = a' ≫ g ≫ π → (∀ σ m, a ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m) = a' ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m)) → ∃ hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π, ∀ σ (i : ℕ), F.step (a' ≫ g) hx' σ i = F.step (a ≫ g) rfl σ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F Mc T g hg t htf ht R _ f K _ a a' hπ hP
  have hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π := by simpa only [Category.assoc] using hπ.symm
  refine ⟨hx', fun σ i => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing F.cover (a ≫ g)
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing F.cover (a' ≫ g)
  have hM : ⊤ ≤ ((a ≫ g) ≫ π) ⁻¹ᵁ Mc.U := fun p _ => hg (Set.mem_univ (a p))
  have hM' : ⊤ ≤ ((a' ≫ g) ≫ π) ⁻¹ᵁ Mc.U := fun p _ => hg (Set.mem_univ (a' p))
  have hU : ⊤ ≤ (a ≫ g) ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U) := le_preimage_inf hk hM
  have hU' : ⊤ ≤ (a' ≫ g) ⁻¹ᵁ (F.U k' ⊓ π ⁻¹ᵁ Mc.U) := le_preimage_inf hk' hM'
  have e1 : F.vecAt k (a ≫ g) hk rfl σ =
      (vec Mc _ hM).toLinearMap ∘ fun j r => (plkU F Mc k σ).map (ev (a ≫ g) _ hU) r j :=
    funext fun j => Sep.vecAt_eq_vec F Mc k (a ≫ g) hk rfl hM hU σ j
  have e2 : F.vecAt k' (a' ≫ g) hk' hx' σ =
      (vec Mc _ hM).toLinearMap ∘ fun j r => (plkU F Mc k' σ).map (ev (a' ≫ g) _ hU') r j :=
    funext fun j => Sep.vecAt_eq_vec F Mc k' (a' ≫ g) hk' hx' hM hU' σ j
  rw [F.step_eq k' _ hk' hx', F.step_eq k _ hk rfl, e1, e2, Sep.initSpan_comp, Sep.initSpan_comp]
  congr 1
  refine Sep.initSpan_cols_eq _ _ ?_ ?_ i
  · have := F.linearIndependent_vecAt k (a ≫ g) hk rfl σ
    rw [e1] at this
    exact this.of_comp _
  · intro m
    have hj : ⊤ ≤ a ⁻¹ᵁ ((F.LL (ind σ m)).pull g).U (fun _ => k) := by
      exact fun p _ => Set.mem_iInter.2 fun _ => hk (Set.mem_univ p)
    have hj' : ⊤ ≤ a' ⁻¹ᵁ ((F.LL (ind σ m)).pull g).U (fun _ => k') := by
      exact fun p _ => Set.mem_iInter.2 fun _ => hk' (Set.mem_univ p)
    have c1 := GlobalTheory.ZH.SecImm.crd_toProj f (t σ m) (ht σ m) a _ hj
    have c2 := GlobalTheory.ZH.SecImm.crd_toProj f (t σ m) (ht σ m) a' _ hj'
    rw [← hP σ m] at c2
    obtain ⟨u, hu⟩ := GlobalTheory.ZH.CrdCalc.crd_unique c1 c2
    refine ⟨u, fun r => ?_⟩
    have e := hu (Fin.succ (Fintype.equivFin _ r))
    simp only [htf σ m] at e
    rw [Sep.valF_plkLoc F Mc g hg σ m a k hj hU r, Sep.valF_plkLoc F Mc g hg σ m a' k' hj' hU' r] at e
    exact e
