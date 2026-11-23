import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

section Gen

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

private theorem comm_finsum {ι : Type} {T : Module.End A M} {φ : ι → Module.End A M} (h : ∀ i, Commute T (φ i)) :
    Commute T (∑ᶠ i, φ i) := by
  by_cases hf : (Function.support φ).Finite
  · rw [finsum_eq_sum _ hf]
    exact Commute.sum_right _ _ _ fun i _ => h i
  · rw [finsum_of_infinite_support hf]
    exact Commute.zero_right _

private theorem iSup_pres {T : Module.End A M} {P : ℕ → Module.End A M} {S : Submodule A M} (hc : ∀ n, Commute T (P n))
    (hS : ∀ x ∈ S, T x ∈ S) {x : M} (hx : x ∈ ⨆ n, S.comap (P n)) : T x ∈ ⨆ n, S.comap (P n) := by
  refine Submodule.iSup_induction (fun n => S.comap (P n)) (motive := fun y => T y ∈ ⨆ n, S.comap (P n))
    hx ?_ ?_ ?_
  · intro n y hy
    apply Submodule.mem_iSup_of_mem n
    rw [Submodule.mem_comap] at hy ⊢
    have e : P n (T y) = T (P n y) := by
      simpa [Module.End.mul_apply] using (LinearMap.congr_fun (hc n).eq y).symm
    rw [e]
    exact hS _ hy
  · simp
  · intro y z hy hz
    simp only [map_add]
    exact Submodule.add_mem _ hy hz

end Gen

section Fr

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}

variable (A m) in

private abbrev R (g : Ga) : Module.End A (X.Fn A m) := rtr A (Ga × Gp) (Fin m → A) (g, 1)

private theorem comm_rp (g : Ga) (p : Gp) : Commute (R X A m g) (X.rp A m p) := by
  have hc : Commute ((g, 1) : Ga × Gp) (1, p) := by
    show ((g, 1) : Ga × Gp) * (1, p) = (1, p) * (g, 1)
    ext <;> simp
  exact hc.map (rtr A (Ga × Gp) (Fin m → A))

private theorem comm_U (g : Ga) (a : Gp) : Commute (R X A m g) (X.U A m a) := by
  unfold Frame.U Iwa.uOp
  exact comm_finsum fun q => comm_rp X g _

private theorem comm_ra (τ : X.Ub →* GL (Fin m) A) {g : Ga} {u : X.Ub} (h : Commute g (u : Ga)) :
    Commute (R X A m g) (X.ra τ u) := by
  refine LinearMap.ext fun f => funext fun x => ?_
  have e : ((g, 1) : Ga × Gp) * ((u : Ga), 1) = ((u : Ga), 1) * (g, 1) := by
    ext <;> simp [h.eq]
  simp only [Module.End.mul_apply, Frame.ra_apply, R, rtr, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.funLeft_apply, mul_assoc, e]

private theorem valIn_pres [IsLocalRing A] (g : Ga) (k : ℕ) {f : X.Fn A m} (hf : f ∈ X.valIn A m k) :
    R X A m g f ∈ X.valIn A m k := by
  simp only [Frame.valIn, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
  intro x i
  exact hf _ i

variable [IsLocalRing A]

private theorem amb_pres (θ : X.I.T →* Aˣ) (g : Ga) {f : X.Fn A m} (hf : f ∈ X.Amb m θ) : R X A m g f ∈ X.Amb m θ := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ x
    show f (X.glob γ * x * (g, 1)) = f (x * (g, 1))
    rw [mul_assoc]
    exact h1 γ _
  · intro u hu
    have e : X.rp A m u (R X A m g f) = R X A m g (X.rp A m u f) :=
      (LinearMap.congr_fun (comm_rp X g u).eq f).symm
    rw [e, h2 u hu]
  · intro t
    have e : X.rp A m t (R X A m g f) = R X A m g (X.rp A m t f) :=
      (LinearMap.congr_fun (comm_rp X g t).eq f).symm
    rw [e, h3 t, map_smul]
  · intro k
    obtain ⟨c, hc⟩ := h4 k
    refine ⟨c, fun y hy x i => ?_⟩
    show f (x * (1, y) * (g, 1)) i - f (x * (g, 1)) i ∈ _
    have ex : x * (1, y) * (g, 1) = x * (g, 1) * (1, y) := by
      ext <;> simp [mul_assoc]
    rw [ex]
    exact hc y hy _ i

private theorem fix_pres (τ : X.Ub →* GL (Fin m) A) (U : Subgroup X.Ub) {g : Ga}
    (hU : ∀ u ∈ U, ∃ u' ∈ U, (u' : Ga) = g⁻¹ * u * g ∧ τ u' = τ u) {f : X.Fn A m} (hf : f ∈ fixd (X.ra τ) U) :
    R X A m g f ∈ fixd (X.ra τ) U := by
  intro u hu
  obtain ⟨u', hu', e1, e2⟩ := hU u hu
  funext x
  have hfx := congrFun (hf u' hu') (x * (g, 1))
  have ex : x * (g, 1) * ((u' : Ga), 1) = x * ((u : Ga), 1) * (g, 1) := by
    rw [e1]; ext <;> simp [mul_assoc]
  rw [Frame.ra_apply, ex, e2] at hfx
  rw [Frame.ra_apply]
  exact hfx

private theorem ord_pres (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) {g : Ga}
    (hU : ∀ u ∈ U, ∃ u' ∈ U, (u' : Ga) = g⁻¹ * u * g ∧ τ u' = τ u) {f : X.Fn A m} (hf : f ∈ X.Ord τ θ U) :
    R X A m g f ∈ X.Ord τ θ U := by
  simp only [Frame.Ord, Frame.Sp, Submodule.mem_inf, Submodule.mem_iInf] at hf ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨⟨amb_pres X θ g h1, fix_pres X τ U hU h2⟩, fun k => ?_⟩
  refine iSup_pres (fun n => ?_) (fun x hx => valIn_pres X g k hx) (h3 k)
  exact ((comm_U X g X.I.z).pow_right (n + 1)).sub_right (Commute.one_right _)

end Fr

section Set

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (A : Type) [CommRing A] [Algebra c.O A]

private theorem tr_op {g : H.Ga} (hg : Norm H g) (i : H.Op) : Commute (trA H A g) (H.op A i) := by
  rcases i with x | x
  · change Commute (R H.X A H.m g) (sphOp ((H.X.ra (H.τA A)).comp (H.sec x.1)) (x.2 + 1))
    unfold sphOp dc
    refine comm_finsum fun q => ?_
    exact comm_ra H.X (H.τA A) (hg.sph x.1 x.1.2 _)
  · change Commute (R H.X A H.m g) (H.X.U A H.m _)
    exact comm_U H.X g _

variable {A} [IsLocalRing A] (θ : H.X.I.T →* Aˣ)

private theorem tr_Ord {g : H.Ga} (hg : Norm H g) (K : H.Lev) {f : H.X.Fn A H.m} (hf : f ∈ H.X.Ord (H.τA A) θ (H.lev K)) :
    trA H A g f ∈ H.X.Ord (H.τA A) θ (H.lev K) :=
  ord_pres H.X (H.τA A) θ (H.lev K) (fun u hu => by
    obtain ⟨u', h1, h2, h3⟩ := hg.lev K u hu
    exact ⟨u', h1, h2, congrArg (Matrix.GeneralLinearGroup.map (algebraMap c.O A)) h3⟩) hf

private theorem tr_MK {g : H.Ga} (hg : Norm H g) (a : H.Op → c.O) (K : H.Lev) {f : H.X.Fn A H.m} (hf : f ∈ H.MK θ a K) :
    trA H A g f ∈ H.MK θ a K := by
  unfold HSet.MK locPart at hf ⊢
  rw [Submodule.mem_inf, Submodule.mem_iInf] at hf
  rw [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨h1, h2⟩ := hf
  refine ⟨tr_Ord H θ hg K h1, fun i => ?_⟩
  refine (Submodule.mem_iInf _).mpr fun k => ?_
  have h2' := (Submodule.mem_iInf _).mp (h2 i) k
  have hle : ∀ x ∈ maximalIdeal A ^ k • H.X.Ord (H.τA A) θ (H.lev K),
      trA H A g x ∈ maximalIdeal A ^ k • H.X.Ord (H.τA A) θ (H.lev K) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      rw [map_smul]
      exact Submodule.smul_mem_smul hr (tr_Ord H θ hg K hy)
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  refine iSup_pres (fun n => ?_) hle h2'
  refine Commute.pow_right ?_ n
  refine (tr_op H A hg i).sub_right ?_
  exact (Algebra.commutes _ _).symm

private theorem tr_fix {g : H.Ga} (h : ∃ u ∈ H.UQ, (u : H.Ga) = g ∧ H.τ u = 1) (K : H.Lev) {f : H.X.Fn A H.m}
    (hf : f ∈ H.X.Ord (H.τA A) θ (H.lev K)) : trA H A g f = f := by
  obtain ⟨u, hu, e1, e2⟩ := h
  simp only [Frame.Ord, Frame.Sp, Submodule.mem_inf] at hf
  have hmem : u ∈ H.lev K := by
    unfold HSet.lev
    exact Subgroup.mem_sup_left hu
  have hfix := hf.1.2 u hmem
  funext x
  have hx := congrFun hfix x
  change ((H.τA A u : GL (Fin H.m) A) : Matrix (Fin H.m) (Fin H.m) A) *ᵥ f (x * ((u : H.Ga), 1)) = f x at hx
  have hτ' : H.τA A u = 1 := by
    show Matrix.GeneralLinearGroup.map (algebraMap c.O A) (H.τ u) = 1
    rw [e2, map_one]
  rw [hτ', Units.val_one, Matrix.one_mulVec, e1] at hx
  exact hx

end Set

private theorem opE_eq {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) (a : G →₀ ℤ)
    (x : W) : opE ρ a x = ∑ g ∈ a.support, a g • ρ g x := by
  simp [opE, Finsupp.sum, LinearMap.sum_apply]

end UpperTheory.V.Z.Desc.V0

open UpperTheory.V.Z.Desc.V0

theorem UpperTheory.V.Z.Desc.V0.eEx :
    EEx := by
  unfold EEx
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ K a₀ _ G _ K₀ K₁ β a N hK hE hN
  let ρ : Representation A G (H.X.Fn A H.m) := (trA H A).comp β
  let E : Module.End A (H.X.Fn A H.m) := opE ρ a
  have hMOrd : ∀ f ∈ H.MK θ a₀ K, f ∈ H.X.Ord (H.τA A) θ (H.lev K) := by
    intro f hf
    unfold HSet.MK locPart at hf
    exact (Submodule.mem_inf.mp hf).1
  have hρM : ∀ g ∈ K₀, ∀ f ∈ H.MK θ a₀ K, ρ g f ∈ H.MK θ a₀ K :=
    fun g hg f hf => tr_MK H θ (hK.norm g hg) a₀ K hf
  have hEM : ∀ f ∈ H.MK θ a₀ K, E f ∈ H.MK θ a₀ K := by
    intro f hf
    show opE ρ a f ∈ H.MK θ a₀ K
    rw [opE_eq]
    refine Submodule.sum_mem _ fun g hg => ?_
    exact zsmul_mem (hρM g (hE.supp g hg) f hf) _
  have hfixM : ∀ f ∈ H.MK θ a₀ K, f ∈ fixd ρ K₁ := by
    intro f hf g hg
    exact tr_fix H θ (hK.triv g hg) K (hMOrd f hf)
  have hsq : ∀ f ∈ H.MK θ a₀ K, E (E f) = N • E f :=
    fun f hf => hE.sq A (H.X.Fn A H.m) ρ f (hfixM f hf)
  have hcomm : ∀ i f, E (H.op A i f) = H.op A i (E f) := by
    intro i f
    show opE ρ a (H.op A i f) = H.op A i (opE ρ a f)
    rw [opE_eq, opE_eq, map_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [map_zsmul]
    congr 1
    exact LinearMap.congr_fun (tr_op H A (hK.norm g (hE.supp g hg)) i).eq f
  obtain ⟨u, hu⟩ := hN
  let e : Module.End A (H.MK θ a₀ K) := (↑u⁻¹ : A) • E.restrict hEM
  refine ⟨e, ?_, ?_, ?_⟩
  · intro m
    show N • ((↑u⁻¹ : A) • E m) = E m
    rw [← Nat.cast_smul_eq_nsmul A, ← hu, smul_smul, Units.mul_inv, one_smul]
  · refine LinearMap.ext fun m => Subtype.ext ?_
    show (↑u⁻¹ : A) • E ((↑u⁻¹ : A) • E m) = (↑u⁻¹ : A) • E m
    rw [map_smul, hsq m m.2, ← Nat.cast_smul_eq_nsmul A, ← hu, smul_smul, smul_smul, mul_assoc,
      Units.inv_mul, mul_one]
  · intro t
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute t.2 ?_
    rintro t' ⟨i, hi⟩
    refine LinearMap.ext fun m => Subtype.ext ?_
    show (↑u⁻¹ : A) • E ↑(t' m) = ↑(t' (e m))
    rw [hi m, hi (e m), hcomm]
    show (↑u⁻¹ : A) • H.op A i (E m) = H.op A i ((↑u⁻¹ : A) • E m)
    rw [map_smul]
