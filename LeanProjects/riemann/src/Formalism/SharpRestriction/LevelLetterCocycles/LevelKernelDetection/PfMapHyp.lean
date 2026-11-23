import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section General

variable {LL Ks D₁ D₂ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D₁]
  [Module LL D₁] [AddCommGroup D₂] [Module LL D₂]

theorem Pf_MapHyp_ambMap_coeff (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) (f : Amb LL Ks D₁) (k : ℤ) :
    ((HahnModule.of Ks).symm (ambMap g f)).coeff k = g (((HahnModule.of Ks).symm f).coeff k) :=
  rfl

theorem Pf_MapHyp_ambMap_smul (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) (x : HahnSeries ℤ Ks)
    (f : Amb LL Ks D₁) : ambMap g (x • f) = x • ambMap g f := by
  have hsupp : ((HahnModule.of Ks).symm (ambMap g f)).support ⊆
      ((HahnModule.of Ks).symm f).support := by
    intro k hk
    rw [HahnSeries.mem_support] at hk ⊢
    intro h0
    apply hk
    rw [Pf_MapHyp_ambMap_coeff, h0, map_zero]
  apply HahnModule.ext
  funext k
  rw [HahnModule.coeff_smul_right (y := ambMap g f) ((HahnModule.of Ks).symm f).isPWO_support hsupp,
    Pf_MapHyp_ambMap_coeff, HahnModule.coeff_smul, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_smul, Pf_MapHyp_ambMap_coeff]

theorem Pf_MapHyp_baseChange_tD (h : D₁ →ₗ[LL] D₂) (τ : Ks ≃ₐ[LL] Ks) (a : LL) (y : Ks ⊗[LL] D₁) :
    h.baseChange Ks (a • tD D₁ τ y) = a • tD D₂ τ (h.baseChange Ks y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x d => simp [tD, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  | add y y' hy hy' => simp only [map_add, smul_add, hy, hy']

theorem Pf_MapHyp_grd_ambMap (h : D₁ →ₗ[LL] D₂) (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (f : Amb LL Ks D₁) :
    grd (D := D₂) τ a (ambMap (h.baseChange Ks) f) = ambMap (h.baseChange Ks) (grd (D := D₁) τ a f) := by
  apply HahnModule.ext
  funext i
  change ((a ^ i : LLˣ) : LL) • tD D₂ τ (h.baseChange Ks (cf f i)) =
    h.baseChange Ks (((a ^ i : LLˣ) : LL) • tD D₁ τ (cf f i))
  rw [Pf_MapHyp_baseChange_tD]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

variable {W : LocWach PD LL O v n} {T₁ T₂ : LocLat G Qp LL O}
variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {c : ZMod n}

theorem memD_holds (W : LocWach PD LL O v n) (F : LatHom T₁.L T₂.L) (c : ZMod n) : MemD W F c := by
  intro x hx
  have hA : ∀ (g : G) (y : T₁.V ⊗[Qp] B),
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (actVB PD T₁.ρ g y) =
        actVB PD T₂.ρ g (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w b => simp [actVB, AlgebraTensorModule.map_tmul, F.equiv]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  have hB : ∀ (c' : K₀) (y : T₁.V ⊗[Qp] B),
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)
          (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c' y) =
        mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c'
          (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
    intro c' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w b => simp [mulVB, AlgebraTensorModule.map_tmul]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  simp only [DcrisL, Dcris, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  exact ⟨fun g => by rw [← hA, hx.1 g], fun c' => by rw [← hB, hx.2 c', map_smul]⟩

theorem smul_holds {F : LatHom T₁.L T₂.L} (memD : MemD W F c) :
    ∀ (s : ℕ) (x : HahnSeries ℤ (KsW W s)) (f : Amb LL (KsW W s) (Dc W T₁ c)),
      ambF memD s (x • f) = x • ambF memD s f :=
  fun s x f => Pf_MapHyp_ambMap_smul ((dmapOf memD).baseChange (KsW W s)) x f

theorem inv_holds {F : LatHom T₁.L T₂.L} (memD : MemD W F c) :
    ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T₁ c)), (levW W uZ ιZ s).Inv f →
      (levW W uZ ιZ s).Inv (ambF memD s f) := by
  intro s f hf j
  have hj : (levW W uZ ιZ s).δ j f = f := hf j
  show (levW W uZ ιZ s).δ j (ambF memD s f) = ambF memD s f
  rw [Level.δ] at hj ⊢
  unfold ambF
  rw [Pf_MapHyp_grd_ambMap, hj]

theorem mapHyp_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (F : LatHom T₁.L T₂.L)
    (c : ZMod n) : MapHyp hR uZ ιZ F c :=
  ⟨memD_holds W F c, smul_holds (memD_holds W F c), inv_holds (memD_holds W F c)⟩

end Formalism.MainNotions.N.Ln03.Pf
