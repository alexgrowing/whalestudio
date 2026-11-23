import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.Sp

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)

theorem lev_dir (a b : H.Lev) : ∃ k, H.lev k ≤ H.lev a ∧ H.lev k ≤ H.lev b := by
  refine ⟨⟨fun q => a.1 q ⊓ b.1 q, fun q => ⟨(a.2 q).1.inter (b.2 q).1,
    (a.2 q).2.inter_right ((b.1 q).isClosed_of_isOpen (b.2 q).1)⟩⟩, ?_, ?_⟩
  · exact sup_le_sup_left (iSup_mono fun q => Subgroup.map_mono inf_le_left) _
  · exact sup_le_sup_left (iSup_mono fun q => Subgroup.map_mono inf_le_right) _

theorem mem_fixd_lev {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A H.X.Ub M) (K : H.Lev) (v : M) :
    v ∈ fixd ρ (H.lev K) ↔ (∀ u ∈ H.UQ, ρ u v = v) ∧ ∀ q, ∀ g ∈ K.1 q, ρ (H.sec (H.wq q) g) v = v := by
  refine ⟨fun h => ⟨fun u hu => h u (Subgroup.mem_sup_left hu), fun q g hg => h _
    (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q ⟨g, hg, rfl⟩))⟩, fun h u hu => ?_⟩
  let S : Subgroup H.X.Ub :=
    { carrier := {u | ρ u v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change ρ a⁻¹ v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have : H.lev K ≤ S := sup_le h.1 (iSup_le fun q => by
    rintro _ ⟨g, hg, rfl⟩
    exact h.2 q g hg)
  exact this hu

private theorem comm_app {A M G : Type} [CommRing A] [AddCommGroup M] [Module A M] [Group G] (ρ : Representation A G M) {a b : G}
    (h : Commute a b) (v : M) : ρ a (ρ b v) = ρ b (ρ a v) := by
  rw [← Module.End.mul_apply, ← map_mul, h.eq, map_mul, Module.End.mul_apply]

theorem lev_act (hH : H.Ax) (K : H.Lev) (q : H.Q) (g : GLw n (H.wq q)) : ∃ K' : H.Lev,
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A H.X.Ub M),
      ∀ v ∈ fixd ρ (H.lev K), ρ (H.sec (H.wq q) g) v ∈ fixd ρ (H.lev K') := by
  classical
  let e : GLw n (H.wq q) ≃ₜ GLw n (H.wq q) := (Homeomorph.mulRight g).trans (Homeomorph.mulLeft g⁻¹)
  refine ⟨⟨Function.update K.1 q ((K.1 q).comap (MulAut.conj g⁻¹).toMonoidHom), fun q' => ?_⟩, fun A M _ _ _ ρ v hv => ?_⟩
  · by_cases h : q' = q
    · subst h
      rw [Function.update_self]
      have : (((K.1 q').comap (MulAut.conj g⁻¹).toMonoidHom : Subgroup _) : Set (GLw n (H.wq q'))) = e ⁻¹' (K.1 q') := by
        ext x
        simp [e, mul_assoc]
      rw [this]
      exact ⟨(K.2 q').1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q').2⟩
    · rw [Function.update_of_ne h]
      exact K.2 q'
  · rw [mem_fixd_lev] at hv ⊢
    refine ⟨fun u hu => ?_, fun q' k hk => ?_⟩
    · rw [comm_app ρ (hH.Q_UQ q u hu g), hv.1 u hu]
    · by_cases h : q' = q
      · subst h
        simp only [Function.update_self] at hk
        have := hv.2 q' _ hk
        have e1 := LinearMap.congr_fun (map_mul (ρ.comp (H.sec (H.wq q'))) k g) v
        have e2 := LinearMap.congr_fun (map_mul (ρ.comp (H.sec (H.wq q'))) g ((MulAut.conj g⁻¹).toMonoidHom k)) v
        have e3 : g * (MulAut.conj g⁻¹).toMonoidHom k = k * g := by simp [mul_assoc]
        rw [e3] at e2
        exact e1.symm.trans (e2.trans (congrArg (ρ (H.sec (H.wq q') g)) this))
      · simp only [Function.update_of_ne h] at hk
        rw [comm_app ρ (hH.Q_Q q' q h k g), hv.2 q' k hk]

theorem lev_sph (w : W.Plc L) (j : ℕ) : ∃ (κ : Type) (_ : Fintype κ) (u : κ → H.X.Ub),
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A H.X.Ub M),
      sphOp (ρ.comp (H.sec w)) j = ∑ q, ρ (u q) ∧ (H.Ax → w ∈ H.Wp →
      ∀ K, ∀ v ∈ fixd ρ (H.lev K), (∑ q, ρ (u q)) v ∈ fixd ρ (H.lev K)) := by
  have hfin := (sphComm (w.adicCompletion L) n ℤ ℤ 1).1 (al _ n j)
  letI := hfin.fintype
  refine ⟨MulAction.orbit (KO (w.adicCompletion L) (Fin n)) ((al _ n j : GLw n w) : GLw n w ⧸ KO (w.adicCompletion L) (Fin n)),
    inferInstance, fun q => H.sec w q.1.out, fun A M _ _ _ ρ => ?_⟩
  have h1 : sphOp (ρ.comp (H.sec w)) j = ∑ q : MulAction.orbit (KO (w.adicCompletion L) (Fin n))
      ((al _ n j : GLw n w) : GLw n w ⧸ KO (w.adicCompletion L) (Fin n)), ρ (H.sec w q.1.out) := by
    rw [sphOp, dc, finsum_eq_sum_of_fintype]
    rfl
  refine ⟨h1, fun hH hw K v hv => ?_⟩
  rw [mem_fixd_lev] at hv ⊢
  have h2 := (dcSum A _ M (ρ.comp (H.sec w)) _ _ _ hfin).2.1 v fun k hk => hv.1 _ (hH.W_le w hw ⟨k, hk, rfl⟩)
  have h3 : ∀ u : H.X.Ub, (∀ g, Commute u (H.sec w g)) → ρ u v = v → ρ u (sphOp (ρ.comp (H.sec w)) j v) =
      sphOp (ρ.comp (H.sec w)) j v := by
    intro u hu hv
    rw [h1, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [comm_app ρ (hu _), hv]
  rw [← h1]
  refine ⟨fun u hu => ?_, fun q g hg => h3 _ (hH.sectionsCommuteAtSplit q w hw g) (hv.2 q g hg)⟩
  obtain ⟨k, hk, u', hu', rfl, hc⟩ := hH.W_dec w hw u hu
  exact (LinearMap.congr_fun (map_mul ρ (H.sec w k) u') _).trans
    ((congrArg (ρ (H.sec w k)) (h3 u' hc (hv.1 u' hu'))).trans (h2 k hk))

section Gl

variable {V : Type} [Fintype V] (S : V → W.Plc L)

private theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero (M : Submonoid (iwS n S).T) (t : (iwS n S).T) (y : ∀ v, Fin n → Uo ((S v).adicCompletion L))
    (hy : ∀ v, (t : GV n S) v = (List.ofFn fun i => (eT _ n i (y v i) : GLw n (S v))).prod)
    (h : ∀ v i, eV n S v i (y v i) ∈ M) : t ∈ M := by
  classical
  have : (t : GV n S) ∈ M.map (iwS n S).T.subtype := by
    rw [← Finset.noncommProd_mulSingle (t : GV n S)]
    refine Submonoid.noncommProd_mem _ _ _ _ fun v _ => ?_
    change MonoidHom.mulSingle (fun v : V => GLw n (S v)) v ((t : GV n S) v) ∈ _
    rw [hy, map_list_prod]
    refine list_prod_mem fun x hx => ?_
    rw [List.map_ofFn, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨_, h v i, ?_⟩
    change (eV n S v i (y v i)).1 = Pi.mulSingle v _
    unfold eV
    congr
  obtain ⟨s, hs, e⟩ := this
  rwa [← Subtype.ext e]

theorem torus_mem_submonoid_of_elementaryTorus (M : Submonoid (iwS n S).T) (h : ∀ v i y, eV n S v i y ∈ M) (t : (iwS n S).T) : t ∈ M := by
  choose y hy _ using fun v => (glBridge ((S v).adicCompletion L) n ℂ 1).2.2.2.2.2.2.2.2.2 ⟨t.1 v, t.2 v trivial⟩
  exact add_one_pow_eq_ringHom_image_add_prime_mul_zero S M t y hy fun v i => h v i _

theorem gen_Tc (M : Submonoid (iwS n S).T) (e : ℕ)
    (h : ∀ v i (y : Uo ((S v).adicCompletion L)), (y : ((S v).adicCompletion L)ˣ) ∈ Uc _ (e + 1) → eV n S v i y ∈ M)
    (t : (iwS n S).T) (ht : (t : GV n S) ∈ (iwS n S).Tc e) : t ∈ M := by
  choose y hy hy' using fun v => (glBridge ((S v).adicCompletion L) n ℂ 1).2.2.2.2.2.2.2.2.2 ⟨t.1 v, t.2 v trivial⟩
  exact add_one_pow_eq_ringHom_image_add_prime_mul_zero S M t y hy fun v i => h v i _ (hy' v e (ht v trivial) i)

theorem Uc_anti (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : ℕ}
    (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun y hy => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hy ⊢
  exact Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right h (Ideal.Quotient.eq.1 (hy.trans (map_one _).symm)) : (y : 𝒪[k]) - 1 ∈ _)

theorem alV_mem (v : V) (j : ℕ) : alV n S v j ∈ (iwS n S).P := by
  classical
  intro v' _
  unfold alV
  by_cases h : v' = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact al_mem _ n j
  · rw [Pi.mulSingle_eq_of_ne h]
    exact Submonoid.one_mem _

theorem algPow_one (w : W.Plc L) (h : (L →+* Qbar l) → ℤ) : algPow w h 1 = 1 := by
  simp [algPow]

variable (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (χ : (iwS n S).Tf →* ℂˣ)
  (hχ : ∀ (t : (iwS n S).Tf) (y : ∀ v, Fin n → ((S v).adicCompletion L)ˣ), (∀ v, (t : GV n S) v = diagT _ (Fin n) (y v)) →
    (χ t : ℂ) = ι (∏ v, ∏ i, algPow (S v) (lowW lam i) (y v i : (S v).adicCompletion L)))
include hχ

theorem chi_single [DecidableEq V] (t : (iwS n S).Tf) (v : V) (y : Fin n → ((S v).adicCompletion L)ˣ)
    (ht : (t : GV n S) = Pi.mulSingle v (diagT _ (Fin n) y)) :
    (χ t : ℂ) = ι (∏ i, algPow (S v) (lowW lam i) (y i : (S v).adicCompletion L)) := by
  rw [hχ t (Pi.mulSingle v y), Finset.prod_eq_single v]
  · simp
  · intro v' _ h
    simp [Pi.mulSingle_eq_of_ne h, algPow_one]
  · simp
  · intro v'
    rw [ht]
    by_cases h : v' = v
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]

theorem chi_eV (v : V) (i : Fin n) (y : Uo ((S v).adicCompletion L)) :
    (χ ⟨eV n S v i y, (iwS n S).T_le (eV n S v i y).2⟩ : ℂ) =
      ι (algPow (S v) (lowW lam i) ((y : ((S v).adicCompletion L)ˣ) : (S v).adicCompletion L)) := by
  classical
  rw [chi_single S ι lam χ hχ _ v (Pi.mulSingle i y.1) (by unfold eV; congr), Finset.prod_eq_single i]
  · simp
  · intro v' _ h
    simp [Pi.mulSingle_eq_of_ne h, algPow_one]
  · simp

theorem chi_alV (v : V) (j : ℕ) :
    (χ ⟨alV n S v j, (iwS n S).P_le _ (alV_mem S v j)⟩ : ℂ) =
      ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j, algPow (S v) (lowW lam i)
        ((unif ((S v).adicCompletion L) : ((S v).adicCompletion L)ˣ) : (S v).adicCompletion L)) := by
  classical
  rw [chi_single S ι lam χ hχ _ v (fun i => unif _ ^ (if (i : ℕ) < j then (1 : ℤ) else 0)) (by unfold alV; congr),
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp [algPow_one]

omit hχ in
theorem weightChar_central_eq_prod_uniformizerDiag : χ ⟨(iwS n S).z, (iwS n S).P_le _ (iwS n S).z_mem⟩ =
    ∏ v, ∏ j ∈ Finset.range n, χ ⟨alV n S v j, (iwS n S).P_le _ (alV_mem S v j)⟩ := by
  classical
  let D : (∀ v, Fin n → ((S v).adicCompletion L)ˣ) →* (iwS n S).Tf :=
    { toFun := fun y => ⟨fun v => diagT _ (Fin n) (y v), fun v _ => ⟨_, rfl⟩⟩
      map_one' := Subtype.ext (funext fun v => map_one _)
      map_mul' := fun _ _ => Subtype.ext (funext fun v => map_mul _ _ _) }
  have h1 : ∀ v j, (⟨alV n S v j, (iwS n S).P_le _ (alV_mem S v j)⟩ : (iwS n S).Tf) =
      D (Pi.mulSingle v fun i => unif _ ^ (if (i : ℕ) < j then (1 : ℤ) else 0)) := by
    intro v j
    refine Subtype.ext (funext fun v' => ?_)
    change alV n S v j v' = diagT _ (Fin n) _
    unfold alV
    by_cases h : v' = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      rfl
    · simp [Pi.mulSingle_eq_of_ne h]
  have h2 : (⟨(iwS n S).z, (iwS n S).P_le _ (iwS n S).z_mem⟩ : (iwS n S).Tf) =
      D fun v i => unif _ ^ ((n : ℤ) - 1 - (i : ℕ)) := rfl
  simp only [h1, h2]
  change (χ.comp D) _ = ∏ v, ∏ j ∈ Finset.range n, (χ.comp D) _
  simp only [← map_prod]
  congr 1
  funext v i
  rw [Finset.prod_apply, Finset.prod_apply, Finset.prod_eq_single v]
  · rw [Finset.prod_apply, Finset.prod_apply]
    simp only [Pi.mulSingle_eq_same]
    have : ∀ N : ℕ, (∏ j ∈ Finset.range N, unif ((S v).adicCompletion L) ^ (if (i : ℕ) < j then (1 : ℤ) else 0)) =
        unif _ ^ ((N - 1 - i : ℕ) : ℤ) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.prod_range_succ, ih, ← zpow_add]
        congr 1
        split_ifs <;> omega
    rw [this]
    congr 1
    have := i.2
    omega
  · intro v' _ h
    rw [Finset.prod_apply, Finset.prod_apply]
    simp [Pi.mulSingle_eq_of_ne h.symm]
  · simp

end Gl

end UpperTheory.V.Hi.Sp
