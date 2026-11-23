import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hiC_sum {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (x : H) (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite) (v : M) :
    dc ρ K K x v = ∑ q ∈ hfin.toFinset, ρ q.out v := by
  rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ hfin,
    LinearMap.sum_apply]

private theorem hiC_comm {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (x : H) (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite)
    (T : Module.End A M) (hT : ∀ g v, T (ρ g v) = ρ g (T v)) (v : M) : T (dc ρ K K x v) = dc ρ K K x (T v) := by
  rw [hiC_sum ρ K x hfin, hiC_sum ρ K x hfin, map_sum]
  exact Finset.sum_congr rfl fun q _ => hT _ _

private theorem hiC_orb {H : Type} [Group H] (K : Subgroup H) (x y : H) :
    (y : H ⧸ K) ∈ MulAction.orbit K (x : H ⧸ K) ↔ ∃ k ∈ K, (k * x)⁻¹ * y ∈ K := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, k.2, QuotientGroup.eq.mp hk⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, hk⟩, QuotientGroup.eq.mpr h⟩

private theorem hiC_equiv {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (ρ' : Representation A H' M) (K : Subgroup H) (K' : Subgroup H') (e : H' ≃* H)
    (he : ∀ g, e g ∈ K ↔ g ∈ K') (hρ : ∀ g, ρ' g = ρ (e g)) (x : H')
    (hfin' : (MulAction.orbit K' (x : H' ⧸ K')).Finite) (hfin : (MulAction.orbit K (e x : H ⧸ K)).Finite)
    (v : M) (hv : v ∈ fixd ρ K) : dc ρ' K' K' x v = dc ρ K K (e x) v := by
  classical
  have hq : ∀ a b : H', ((e a : H) : H ⧸ K) = (e b : H) ↔ (a : H' ⧸ K') = b := fun a b => by
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul, he]
  have ho : ∀ y : H', ((e y : H) : H ⧸ K) ∈ MulAction.orbit K (e x : H ⧸ K) ↔
      (y : H' ⧸ K') ∈ MulAction.orbit K' (x : H' ⧸ K') := fun y => by
    rw [hiC_orb, hiC_orb]
    constructor
    · rintro ⟨k, hk, h⟩
      obtain ⟨k, rfl⟩ := e.surjective k
      exact ⟨k, (he k).1 hk, (he _).1 (by simpa using h)⟩
    · rintro ⟨k, hk, h⟩
      exact ⟨e k, (he k).2 hk, by simpa using (he _).2 h⟩
  rw [hiC_sum ρ' K' x hfin', (dcSum A H M ρ K K (e x) hfin).1 (hfin'.toFinset.image fun q => e q.out) ?_ ?_ v hv,
    Finset.sum_image]
  · exact Finset.sum_congr rfl fun q _ => by rw [hρ]
  · intro p _ q _ h
    exact Quotient.out_injective (e.injective h)
  · intro y hy
    obtain ⟨q, hq', rfl⟩ := Finset.mem_image.1 hy
    rw [ho, QuotientGroup.out_eq']
    exact hfin'.mem_toFinset.1 hq'
  · intro q hq'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := e.surjective y
    refine ⟨e (y : H' ⧸ K').out, ⟨Finset.mem_image.2 ⟨_, hfin'.mem_toFinset.2 ((ho y).1 hq'), rfl⟩, ?_⟩, ?_⟩
    · rw [hq, QuotientGroup.out_eq']
    · rintro z ⟨hz, h⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
      rw [hq, QuotientGroup.out_eq'] at h
      rw [h]

private def hiC_stab {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (v : M) : Subgroup H where
  carrier := {u | ρ u v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have ha' : ρ a v = v := ha
    have hb' : ρ b v = v := hb
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' {a} ha := by
    have ha' : ρ a v = v := ha
    change ρ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem hiC_ord {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A]
    [IsCNL A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (hθ : X.I.ContChar θ) (U : Subgroup X.Ub)
    {ι : Type} (s : Finset ι) (u : ι → X.Ub) (f : X.Fn A m) (hf : f ∈ X.Ord τ θ U)
    (hfix : ∑ i ∈ s, X.ra τ (u i) f ∈ fixd (X.ra τ) U) : ∑ i ∈ s, X.ra τ (u i) f ∈ X.Ord τ θ U := by
  obtain ⟨-, h2, h3, -⟩ := spStab Γ Ga Gp X A m τ θ hθ
  have hval : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := fun k f => by
    simp [Frame.valIn, Submodule.mem_pi]
  rw [mem_ord_iff] at hf ⊢
  refine ⟨⟨Submodule.sum_mem _ fun q _ => h2 _ f hf.1.1, hfix⟩, fun k => ?_⟩
  obtain ⟨n, hn⟩ := hf.2 k
  have key : ∀ (u : X.Ub) (j : ℕ), X.ra τ u ((X.U A m X.I.z ^ j) f) = (X.U A m X.I.z ^ j) (X.ra τ u f) := by
    intro u j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, h3 _ X.I.z_mem]
  refine ⟨n, ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [← key, ← map_sub]
  rw [hval] at hn ⊢
  intro g i
  rw [Frame.ra_apply]
  simp only [Matrix.mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hn _ j)

section

variable {A U M : Type} [CommRing A] [Group U] [AddCommGroup M] [Module A M] (ρ : Representation A U M)

private theorem hiC_ra {u u' : U} (h : Commute u u') (f : M) : ρ u (ρ u' f) = ρ u' (ρ u f) := by
  rw [← Module.End.mul_apply, ← map_mul, h.eq, map_mul, Module.End.mul_apply]

private theorem hiC_fix {H ι : Type} [Group H] (s : H →* U) (K : Subgroup H) (x : H)
    (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite) (V : Subgroup U) (W : ι → Subgroup U) (h1 : K.map s ≤ V)
    (h2 : ∀ u ∈ V, ∃ k ∈ K, ∃ u' ∈ V, u = s k * u' ∧ ∀ g, Commute u' (s g))
    (h3 : ∀ i, ∀ u ∈ W i, ∀ g, Commute u (s g)) (f : M) (hf : f ∈ fixd ρ (V ⊔ ⨆ i, W i)) :
    dc (ρ.comp s) K K x f ∈ fixd ρ (V ⊔ ⨆ i, W i) := by
  have hc : ∀ u ∈ V ⊔ ⨆ i, W i, (∀ g, Commute u (s g)) → ρ u (dc (ρ.comp s) K K x f) = dc (ρ.comp s) K K x f :=
    fun u hu h => by rw [hiC_comm _ _ _ hfin _ (fun g v => hiC_ra ρ (h g) v), hf u hu]
  have h4 : V ⊔ ⨆ i, W i ≤ hiC_stab ρ (dc (ρ.comp s) K K x f) := by
    refine sup_le (fun u hu => ?_) (iSup_le fun q u hu => ?_)
    · obtain ⟨k, hk, u', hu', rfl, h⟩ := h2 u hu
      refine mul_mem ?_ (hc u' (Subgroup.mem_sup_left hu') h)
      exact (dcSum A _ _ (ρ.comp s) K K x hfin).2.1 f (fun a ha => hf _ (Subgroup.mem_sup_left (h1 ⟨a, ha, rfl⟩))) k hk
    · exact hc _ (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q hu)) (h3 q u hu)
  exact h4

private theorem hiC_two {H H' : Type} [Group H] [Group H'] (s : H →* U) (K : Subgroup H) (x : H)
    (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite) (s' : H' →* U) (K' : Subgroup H') (x' : H')
    (hfin' : (MulAction.orbit K' (x' : H' ⧸ K')).Finite) (h : ∀ g g', Commute (s g) (s' g')) (f : M) :
    dc (ρ.comp s) K K x (dc (ρ.comp s') K' K' x' f) = dc (ρ.comp s') K' K' x' (dc (ρ.comp s) K K x f) :=
  hiC_comm _ _ _ hfin' _ (fun g v => (hiC_comm (ρ.comp s) _ _ hfin (ρ (s' g))
    (fun g' v => hiC_ra ρ (h g' g).symm v) v).symm) f

end

private theorem hiC_dcOrd {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A]
    [IsCNL A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (hθ : X.I.ContChar θ) (U : Subgroup X.Ub)
    {H : Type} [Group H] (s : H →* X.Ub) (K : Subgroup H) (x : H) (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite)
    (f : X.Fn A m) (hf : f ∈ X.Ord τ θ U) (hfix : dc ((X.ra τ).comp s) K K x f ∈ fixd (X.ra τ) U) :
    dc ((X.ra τ).comp s) K K x f ∈ X.Ord τ θ U := by
  rw [hiC_sum _ _ _ hfin] at hfix ⊢
  exact hiC_ord X τ θ hθ U _ (fun q : H ⧸ K => s q.out) f hf hfix

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A]

private theorem hiC_P (v : H.V) (j : ℕ) : alV n H.Sl v j ∈ H.X.I.P := by
  classical
  intro v' _
  unfold alV
  by_cases h : v' = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact al_mem _ n j
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (glIwa ((H.Sl v').adicCompletion L) n).P.one_mem

private theorem hiC_fin (w : W.Plc L) (x : GLw n w) :
    (MulAction.orbit (KO (w.adicCompletion L) (Fin n)) (x : GLw n w ⧸ KO (w.adicCompletion L) (Fin n))).Finite :=
  (sphComm (w.adicCompletion L) n ℤ ℤ (Representation.trivial _ _ _)).1 x

private theorem hiC_KO (hA : H.Ax) (K : H.Lev) (w : W.Plc L) (hw : w ∈ H.Wp) (f : H.X.Fn A H.m)
    (hf : f ∈ fixd (H.X.ra (H.τA A)) (H.lev K)) :
    f ∈ fixd ((H.X.ra (H.τA A)).comp (H.sec w)) (KO (w.adicCompletion L) (Fin n)) := fun u hu =>
  hf _ (Subgroup.mem_sup_left (hA.W_le w hw ⟨u, hu, rfl⟩))

private theorem hiC_Tfix (hA : H.Ax) (K : H.Lev) (w : W.Plc L) (hw : w ∈ H.Wp) (j : ℕ) (f : H.X.Fn A H.m)
    (hf : f ∈ fixd (H.X.ra (H.τA A)) (H.lev K)) :
    sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j f ∈ fixd (H.X.ra (H.τA A)) (H.lev K) := by
  refine hiC_fix (H.X.ra (H.τA A)) (H.sec w) _ _ (hiC_fin w _) H.UQ _ (hA.W_le w hw) (hA.W_dec w hw) ?_ f hf
  rintro q _ ⟨g, -, rfl⟩
  exact hA.sectionsCommuteAtSplit q w hw g

private theorem hiC_TT (hA : H.Ax) (K : H.Lev) (w : W.Plc L) (hw : w ∈ H.Wp) (j : ℕ) (w' : W.Plc L) (hw' : w' ∈ H.Wp) (j' : ℕ)
    (f : H.X.Fn A H.m) (hf : f ∈ fixd (H.X.ra (H.τA A)) (H.lev K)) :
    sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j (sphOp ((H.X.ra (H.τA A)).comp (H.sec w')) j' f) =
      sphOp ((H.X.ra (H.τA A)).comp (H.sec w')) j' (sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j f) := by
  rcases hA.Wm_mul_Wm_comm w hw w' hw' with h | ⟨e, he, h⟩
  · exact hiC_two (H.X.ra (H.τA A)) (H.sec w) _ _ (hiC_fin w _) (H.sec w') _ _ (hiC_fin w' _) h f
  · have he' : ∀ v ∈ fixd (H.X.ra (H.τA A)) (H.lev K), sphOp ((H.X.ra (H.τA A)).comp (H.sec w')) j' v =
        dc ((H.X.ra (H.τA A)).comp (H.sec w)) (KO _ (Fin n)) (KO _ (Fin n)) (e (al _ n j')) v :=
      fun v hv => hiC_equiv _ _ _ _ e he (fun g => congrArg (H.X.ra (H.τA A)) (h g)) _ (hiC_fin w' _) (hiC_fin w _) v
        (hiC_KO H hA K w hw v hv)
    rw [he' f hf, he' _ (hiC_Tfix H hA K w hw j f hf)]
    exact (sphComm _ n A _ _).2.1 _ _ f (hiC_KO H hA K w hw f hf)

private theorem hiC_main [IsCNL A] (hA : H.Ax) (θ : H.X.I.T →* Aˣ) (hθ : H.X.I.ContChar θ) (K : H.Lev) :
    CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) := by
  obtain ⟨-, -, h3, h4, -⟩ := spStab _ _ _ H.X A H.m (H.τA A) θ hθ
  have hUT : ∀ (w : W.Plc L) j a, a ∈ H.X.I.P → ∀ f, H.X.U A H.m a (sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j f) =
      sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j (H.X.U A H.m a f) := fun w j a ha f =>
    hiC_comm _ _ _ (hiC_fin w _) _ (fun g v => (h3 a ha (H.sec w g) v).symm) f
  refine ⟨?_, ?_⟩
  · rintro (x | x) f hf
    · exact hiC_dcOrd H.X _ θ hθ _ (H.sec x.1.1) _ _ (hiC_fin _ _) f hf (hiC_Tfix H hA K _ x.1.2 _ f hf.1.2)
    · exact (h4 _ _ (hiC_P H _ _)).2 f hf
  · rintro (x | x) (y | y) f hf
    · exact hiC_TT H hA K _ x.1.2 _ _ y.1.2 _ f hf.1.2
    · exact (hUT _ _ _ (hiC_P H _ _) f).symm
    · exact hUT _ _ _ (hiC_P H _ _) f
    · have hN : f ∈ fixd (H.X.rp A H.m) H.X.I.N := hf.1.1.2.1
      have p1 := hiC_P H x.1 (x.2 + 1)
      have p2 := hiC_P H y.1 (y.2 + 1)
      have b1 := (uOpMul _ H.X.I A _ (H.X.rp A H.m) _ _ p1 p2 f hN).2.1
      have b2 := (uOpMul _ H.X.I A _ (H.X.rp A H.m) _ _ p2 p1 f hN).2.1
      rw [H.X.I.comm _ (H.X.I.P_le _ p1) _ (H.X.I.P_le _ p2)] at b1
      exact b1.trans b2.symm

end

theorem UpperTheory.V.Hi.hiComm :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ K, CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) ∧ Module.Finite A (H.X.Ord (H.τA A) θ (H.lev K)) ∧ Module.Free A (H.X.Ord (H.τA A) θ (H.lev K)) ∧ ∀ a, CommOn (H.MK θ a K) (H.op A) ∧ Module.Finite A (H.MK θ a K) ∧ Module.Free A (H.MK θ a K) := by
  intro L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ K
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hfi, hfr, -⟩ := ordFree _ _ _ H.X A H.m (H.τA A) θ hθ.cont (H.lev K) (hA.fin K) (hθ.free K)
  have hC := hiC_main H hA θ hθ.cont K
  refine ⟨hC, hfi, hfr, fun a => ?_⟩
  obtain ⟨b1, -, b2, -, b3⟩ := AlgebraTools.AnnihilatorQuotientFinite.locFree A _ _ (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A)
    (fun i => algebraMap c.O A (a i)) hC
  exact ⟨b1, b2, b3 inferInstance⟩
