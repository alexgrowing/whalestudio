import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapFl

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {hR : Ring9 W}

section Letters

variable {T : LocLat G Qp LL O}

theorem galois_action_frobenius_comm (g : G) (z : T.V ⊗[Qp] B) :
    actVB PD T.ρ g (φVB PD (LL := LL) (V := T.V) z) = φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

theorem scalar_mul_frobenius_comm (k : K₀) (z : T.V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) (PD.σ k) (φVB PD (LL := LL) (V := T.V) z) =
      φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [mulVB, φVB, map_mul, PD.φ_K₀]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

theorem frobenius_maps_letter_succ (i : ZMod n) (z : T.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) z ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hz1 hz2 ⊢
  refine ⟨fun g => ?_, fun k => ?_⟩
  · rw [galois_action_frobenius_comm, hz1 g]
  · obtain ⟨k', rfl⟩ := PD.σ_bij.2 k
    have he : W.emb (i + 1) (PD.σ k') = W.emb i k' := by
      have := congrArg (fun f : K₀ →ₐ[Qp] LL => f k') (W.emb_σ i)
      simpa only [AlgHom.comp_apply] using this
    rw [scalar_mul_frobenius_comm, hz2 k', map_smul, he]

theorem frobenius_pow_maps_letter (m : ℕ) (i : ZMod n) (z : T.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ m) z ∈
      DcrisL PD T.ρ (W.emb (i + (m : ZMod n))) := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ, ← add_assoc]
    exact frobenius_maps_letter_succ _ _ ih

theorem lambda_mem_dcris_letter (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (x : C.V)
    (hx : C.t (c - (ell : ZMod n)) x ∈ W.N T) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ ell) (W.cmp T ⟨_, hx⟩) ∈
      DcrisL PD T.ρ (W.emb c) := by
  have h1 : (⟨_, hx⟩ : ↥(W.N T)) = (letE (c - (ell : ZMod n)) : LetA O n) • ⟨_, hx⟩ :=
    Subtype.ext (C.t_letter _ x).symm
  have h2 := frobenius_pow_maps_letter ell _ _ (W.cmp_letter T (c - (ell : ZMod n)) ⟨_, hx⟩)
  rw [sub_add_cancel] at h2
  rw [h1]
  exact h2

theorem lambda_coe_eq_frobenius_pow (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) {r : ℕ} (e : Fin r → C.V)
    (k : Fin r) (hk : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ ell) (W.cmp T ⟨_, hk⟩) := by
  unfold lamOf
  rw [dif_pos hk, dif_pos (lambda_mem_dcris_letter C c ell (e k) hk)]

end Letters

section Coords

variable {T : LocLat G Qp LL O}

theorem coord_t_sum (C : Coord W (baseIdOf hR) T) (i : ZMod n) {ι : Type} (s : Finset ι) (g : ι → C.V) :
    C.t i (∑ l ∈ s, g l) = ∑ l ∈ s, C.t i (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Coord.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Coord.t_add, ih]

theorem coord_t_const_smul (C : Coord W (baseIdOf hR) T) (i : ZMod n) (a : O) (x : C.V) :
    C.t i (PowerSeries.C a • x) = a • C.t i x := by
  rw [C.t_smul, show PowerSeries.C a = algebraMap O (PowerSeries O) a from rfl, AlgHom.commutes,
    algebraMap_smul]

theorem exists_pi0_eq_letPi_mul (hR : Ring9 W) : ∃ u : LetA O n, W.π₀ = (letπ : LetA O n) * u := by
  obtain ⟨w, -, hw⟩ := π₀₁_eq hR
  have hp : 1 ≤ PD.p - 1 := by
    have := PD.hp.two_le
    omega
  refine ⟨fun _ => w * PowerSeries.X ^ (PD.p - 1 - 1), ?_⟩
  funext j
  show W.π₀₁ = PowerSeries.X * (w * PowerSeries.X ^ (PD.p - 1 - 1))
  rw [hw]
  conv_lhs => rw [← Nat.sub_add_cancel hp, pow_succ]
  ring

theorem comparison_pi0_smul_eq_zero (hR : Ring9 W) (y : ↥(W.N T)) : W.cmp T (W.π₀ • y) = 0 := by
  obtain ⟨u, hu⟩ := exists_pi0_eq_letPi_mul hR
  rw [hu, mul_smul]
  exact W.cmp_π T (u • y)

end Coords

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {r₁ r₂ : ℕ}

theorem lambda_of_matrixCongruences (hC : CoordHom C₁ C₂ F) (hD : MemD W F c) (e₁ : Fin r₁ → C₁.V)
    (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (prLIs : ∀ k, (latHomOf hC).f (e₁ k) -
        ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
      E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n)))) :
    ∀ k, dmapOf hD (lamOf C₁ c ell e₁ k) =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lamOf C₂ c ell e₂ l := by
  intro k
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (prLIs k)
  have hX := hyx
  rw [LinearMap.lsmul_apply] at hX
  change (PowerSeries.X : PowerSeries O) • y = hC.f (e₁ k) - ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l at hX
  have hfe : hC.f (e₁ k) =
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l + (PowerSeries.X : PowerSeries O) • y := by
    rw [hX]
    abel
  have ht : C₂.t (c - (ell : ZMod n)) (hC.f (e₁ k)) =
      ∑ l, (LinearMap.toMatrix' P l k) • C₂.t (c - (ell : ZMod n)) (e₂ l) +
        W.π₀ • C₂.t (c - (ell : ZMod n)) y := by
    rw [hfe, Coord.t_add, coord_t_sum, C₂.t_smul, BaseId.d_X]
    simp only [coord_t_const_smul]
  have hy' : C₂.t (c - (ell : ZMod n)) y ∈ W.N T₂ := hy
  have hx : W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)) ∈ W.N T₂ :=
    W.map_N F hC.crys hC.crys' _ (he₁ k)
  have hsplit : (⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩ : ↥(W.N T₂)) =
      ∑ l, (LinearMap.toMatrix' P l k) •
          (⟨C₂.t (c - (ell : ZMod n)) (e₂ l), he₂ l⟩ : ↥(W.N T₂)) +
        W.π₀ • (⟨C₂.t (c - (ell : ZMod n)) y, hy'⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    show W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)) = _
    rw [← hC.coord_hom_map_trace, ht]
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  have hcmp : W.cmp T₂ ⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩ =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) •
        W.cmp T₂ ⟨C₂.t (c - (ell : ZMod n)) (e₂ l), he₂ l⟩ := by
    rw [hsplit, map_add, map_sum, comparison_pi0_smul_eq_zero hR, add_zero]
    simp only [W.cmp_smul]
  have hL : ∀ l, ((lamOf C₂ c ell e₂ l : Dc W T₂ c) : T₂.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
        (W.cmp T₂ ⟨_, he₂ l⟩) := fun l => lambda_coe_eq_frobenius_pow C₂ c ell e₂ l (he₂ l)
  apply Subtype.ext
  calc ((dmapOf hD (lamOf C₁ c ell e₁ k) : Dc W T₂ c) : T₂.V ⊗[Qp] B)
      = pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ ell)
          (W.cmp T₁ ⟨_, he₁ k⟩)) := by
        rw [← lambda_coe_eq_frobenius_pow C₁ c ell e₁ k (he₁ k)]
        rfl
    _ = ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
          (W.cmp T₂ ⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩) := by
        rw [← pfMapFl_φpow F ell, ← W.cmp_map F hC.crys hC.crys' ⟨_, he₁ k⟩ hx]
    _ = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) •
          ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
            (W.cmp T₂ ⟨_, he₂ l⟩) := by
        rw [hcmp, map_sum]
        simp only [map_smul]
    _ = _ := by
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, hL]

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
