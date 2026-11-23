import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Cst

variable {LL Ks D D₂ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
  [AddCommGroup D₂] [Module LL D₂]

theorem mapLocL_cstD_add (d d' : D) :
    cstD (LL := LL) Ks (d + d') = cstD Ks d + cstD Ks d' := by
  simp [cstD, TensorProduct.tmul_add]

theorem mapLocL_cstD_zero : cstD (LL := LL) (D := D) Ks 0 = 0 := by
  simp [cstD]

theorem mapLocL_cstD_sum {ι : Type} (s : Finset ι) (f : ι → D) :
    cstD (LL := LL) Ks (∑ i ∈ s, f i) = ∑ i ∈ s, cstD Ks (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mapLocL_cstD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mapLocL_cstD_add, ih]

theorem mapLocL_C_smul_cstD (x : LL) (d : D) :
    (HahnSeries.C (algebraMap LL Ks x) : HahnSeries ℤ Ks) • cstD (LL := LL) Ks d = cstD Ks (x • d) := by
  apply HahnModule.ext
  funext i
  rw [HahnSeries.C_apply, HahnModule.coeff_single_zero_smul]
  simp only [cstD, Equiv.symm_apply_apply, HahnSeries.coeff_single]
  split_ifs
  · rw [TensorProduct.tmul_smul, algebraMap_smul]
  · rw [smul_zero]

theorem mapLocL_ambMap_cstD (g : Ks ⊗[LL] D →ₗ[Ks] Ks ⊗[LL] D₂) (d : D) :
    ambMap g (cstD (LL := LL) Ks d) = HahnModule.of Ks (HahnSeries.single 0 (g ((1 : Ks) ⊗ₜ[LL] d))) := by
  apply HahnModule.ext
  funext i
  simp only [ambMap, cstD, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply]
  rw [HahnSeries.map_coeff]
  simp only [HahnSeries.coeff_single]
  split_ifs <;> simp

end Cst

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Helpers

theorem mapLocL_ambF_cstD {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}
    (h : MemD W F c) (s : ℕ) (d : Dc W T₁ c) :
    ambF h s (cstD (KsW W s) d) = cstD (KsW W s) (dmapOf h d) := by
  unfold ambF
  rw [mapLocL_ambMap_cstD, LinearMap.baseChange_tmul]
  rfl

theorem mapLocL_cmp_d (hR : Ring9 W) (T : LocLat G Qp LL O) (a : PowerSeries O) (x : ↥(W.N T)) :
    W.cmp T ((baseIdOf hR).d a • x) = algebraMap O LL (PowerSeries.constantCoeff a) • W.cmp T x := by
  set a' : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a
  set π' : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) W.π₀₁
  have ha : a = PowerSeries.X * a' + PowerSeries.C (PowerSeries.constantCoeff a) :=
    PowerSeries.eq_X_mul_shift_add_const a
  have hπ : W.π₀₁ = PowerSeries.X * π' := by
    have := PowerSeries.eq_X_mul_shift_add_const W.π₀₁
    rwa [π₀₁_const hR, map_zero, add_zero] at this
  have hd : (baseIdOf hR).d a = (letπ : LetA O n) * ((fun _ => π') * (baseIdOf hR).d a') +
      algebraMap O (LetA O n) (PowerSeries.constantCoeff a) := by
    funext i
    have hC0 : (PowerSeries.C (PowerSeries.constantCoeff a) : PowerSeries O) =
        algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [BaseId.d_apply]
    conv_lhs => rw [ha, hC0, map_add, map_mul, AlgHom.commutes, (baseIdOf hR).ι_X, hπ]
    simp only [Pi.add_apply, Pi.mul_apply, BaseId.d_apply, letπ, Pi.algebraMap_apply]
    ring
  rw [hd, add_smul, map_add, mul_smul, W.cmp_π, zero_add, algebraMap_smul, W.cmp_smul]

theorem mapLocL_t_sum {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) {ι : Type}
    (s : Finset ι) (f : ι → C.V) : C.t i (∑ l ∈ s, f l) = ∑ l ∈ s, C.t i (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [C.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C.t_add, ih]

theorem mapLocL_map_φVB {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (z : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) (V := T₁.V) z) =
      φVB PD (LL := LL) (V := T₂.V) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapLocL_map_φVB_pow {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (e : ℕ)
    (z : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (((φVB PD (LL := LL) (V := T₁.V)) ^ e) z) =
      ((φVB PD (LL := LL) (V := T₂.V)) ^ e) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, mapLocL_map_φVB, ih, pow_succ', Module.End.mul_apply]

theorem mapLocL_cmp_map {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁}
    {C₂ : Coord W (baseIdOf hR) T₂} {F : LatHom T₁.L T₂.L} (hC : CoordHom C₁ C₂ F) (i : ZMod n)
    {r : ℕ} (x : C₁.V) (hx : C₁.t i x ∈ W.N T₁) (e₂ : Fin r → C₂.V) (he₂ : ∀ l, C₂.t i (e₂ l) ∈ W.N T₂)
    (a : Fin r → PowerSeries O) (ha : hC.f x = ∑ l, a l • e₂ l) :
    AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (W.cmp T₁ ⟨C₁.t i x, hx⟩) =
      ∑ l, algebraMap O LL (PowerSeries.constantCoeff (a l)) • W.cmp T₂ ⟨C₂.t i (e₂ l), he₂ l⟩ := by
  have hy : W.map F ((⟨C₁.t i x, hx⟩ : ↥(W.N T₁)) : W.DD T₁) ∈ W.N T₂ := by
    show W.map F (C₁.t i x) ∈ W.N T₂
    rw [← hC.coord_hom_map_trace]
    exact (latHomOf hC).map_N i x hx
  rw [← W.cmp_map F hC.crys hC.crys' ⟨C₁.t i x, hx⟩ hy]
  have heq : (⟨W.map F ((⟨C₁.t i x, hx⟩ : ↥(W.N T₁)) : W.DD T₁), hy⟩ : ↥(W.N T₂)) =
      ∑ l, (baseIdOf hR).d (a l) • (⟨C₂.t i (e₂ l), he₂ l⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show W.map F (C₁.t i x) = ∑ l, (baseIdOf hR).d (a l) • C₂.t i (e₂ l)
    rw [← hC.coord_hom_map_trace, ha, mapLocL_t_sum]
    simp only [Coord.t_smul]
  rw [heq, map_sum]
  simp only [mapLocL_cmp_d]

theorem mapLocL_lamOf_coe {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ)
    {r : ℕ} (e : Fin r → C.V) (k : Fin r) (hk : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩) := by
  have h1 : W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ ∈ DcrisL PD T.ρ (W.emb (c - (ell : ZMod n))) := by
    have h0 := W.cmp_letter T (c - (ell : ZMod n)) ⟨_, hk⟩
    have hx : ((letE (c - (ell : ZMod n)) : LetA O n) • (⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ : ↥(W.N T))) =
        ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ := Subtype.ext (C.t_letter _ _)
    rwa [hx] at h0
  have h' : ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩) ∈
      DcrisL PD T.ρ (W.emb c) := by
    have h2 := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T (c - (ell : ZMod n)) h1 ell
    rwa [sub_add_cancel] at h2
  unfold lamOf
  rw [dif_pos hk, dif_pos h']

end Helpers

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapLocL_dmap_lam (hC : CoordHom C₁ C₂ F) (Mh : MapHyp hR uZ ιZ F c)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) (k : Fin r₁) :
    dmapOf Mh.memD (lamOf C₁ c ell e₁ k) =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lamOf C₂ c ell e₂ l := by
  obtain ⟨a, ha, hPa⟩ := hP k
  apply Subtype.ext
  rw [Submodule.coe_sum]
  show AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) ((lamOf C₁ c ell e₁ k : Dc W T₁ c) : T₁.V ⊗[Qp] B) = _
  rw [mapLocL_lamOf_coe C₁ c ell e₁ k (he₁ k), mapLocL_map_φVB_pow,
    mapLocL_cmp_map hC _ (e₁ k) (he₁ k) e₂ he₂ a ha, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Submodule.coe_smul, mapLocL_lamOf_coe C₂ c ell e₂ l (he₂ l), hPa l]

theorem loclComm_holds (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hlam₁ : lam₁ = lamOf C₁ c ell e₁) (hlam₂ : lam₂ = lamOf C₂ c ell e₂)
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    ∀ s < ell, ∀ y : Fin r₁ → PowerSeries O,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
          ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s y) =
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (E.extL P y) := by
  subst hlam₁ hlam₂
  intro s _ y
  apply prL_inj
  intro s' hs'
  erw [prL_of_lt s' hs', prL_of_lt s' hs']
  change ambF Mh.memD s' (locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (lamOf C₁ c ell e₁) s' y) =
    locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (lamOf C₂ c ell e₂) s' (E.extL P y)
  have hk : ∀ k, ambF Mh.memD s' (cstD (KsW W s') (lamOf C₁ c ell e₁ k)) =
      ∑ l, HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' (PowerSeries.C (LinearMap.toMatrix' P l k))) •
        cstD (KsW W s') (lamOf C₂ c ell e₂ l) := by
    intro k
    rw [mapLocL_ambF_cstD, mapLocL_dmap_lam hC Mh e₁ e₂ P he₁ he₂ hP k, mapLocL_cstD_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Hy₂.rhoC, HahnSeries.ofPowerSeries_C, mapLocL_C_smul_cstD]
  have hext : ∀ l, E.extL P y l = ∑ k, PowerSeries.C (LinearMap.toMatrix' P l k) * y k := by
    intro l
    simp [E.extL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp only [locLF]
  rw [Mh.smul, map_sum]
  congr 1
  simp only [Mh.smul, hk, hext, map_sum, map_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem prLIs_holds (hC : CoordHom C₁ C₂ F) {r₁ r₂ : ℕ}
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    ∀ k, (latHomOf hC).f (e₁ k) -
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
    E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n))) := by
  intro k
  obtain ⟨a, ha, hPa⟩ := hP k
  refine Submodule.mem_map.2 ⟨∑ l, (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a l)) • e₂ l,
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (he₂ l), ?_⟩
  rw [LinearMap.lsmul_apply, Finset.smul_sum, ha, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, hPa l, ← sub_smul]
  congr 1
  rw [eq_sub_iff_add_eq]
  exact (PowerSeries.eq_X_mul_shift_add_const (a l)).symm

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
