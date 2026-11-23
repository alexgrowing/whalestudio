import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsMore

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKW.SplitChar

open Filter Topology
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open GlobalTheory.UnRep GlobalTheory.SplitCharTrivial GlobalTheory.SplitIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_AE {x : ℕ → AEF F E} {x₀ : AEF F E}
    (h1 : Tendsto (fun k => infPartF F E (x k)) atTop (𝓝 (infPartF F E x₀)))
    (h2 : Tendsto (fun k => finPartF F E (x k)) atTop (𝓝 (finPartF F E x₀))) : Tendsto x atTop (𝓝 x₀) := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have h : ∀ z, e.symm (infPartF F E z, finPartF F E z) = z := fun z => by
    have : (infPartF F E z, finPartF F E z) = e z := Prod.ext (he z).1.symm (he z).2.symm
    rw [this]
    exact e.symm_apply_apply z
  have := (hc.tendsto _).comp (h1.prodMk_nhds h2)
  rw [h] at this
  exact this.congr fun k => h _

theorem parts_inj (x y : AEF F E) (h1 : infPartF F E x = infPartF F E y) (h2 : finPartF F E x = finPartF F E y) :
    x = y :=
  sub_eq_zero.1 (GlobalTheory.SplitDetCharF.adele_tensor_ext _ (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self]))

variable (E) in

def fj : Af F →ₙ+* AEF F E where
  toFun α := pairA F 0 α ⊗ₜ[F] (1 : E)
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' x y := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm rfl
  map_mul' x y := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_zero _).symm rfl

theorem cA_tmul (σ : E →ₐ[F] E) (a : AF F) (x : E) : cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl

theorem cA_fj (σ : E →ₐ[F] E) (α : Af F) : cAF σ (fj E α) = fj E α := by
  show cAF σ (_ ⊗ₜ _) = _
  rw [cA_tmul, map_one]; rfl

theorem afext {a b : Af F} (h : ∀ v, evalV F v a = evalV F v b) : a = b := Subtype.ext (funext h)

theorem singleV_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (α : Af F) :
    α * singleV F v y = singleV F v (evalV F v α * y) := afext fun w => by
  by_cases hw : w = v
  · subst hw; simp only [map_mul, evalV_singleV_same]
  · simp only [map_mul, evalV_singleV_ne _ v _ hw, mul_zero]

variable (E) in

abbrev pl (v : HeightOneSpectrum (𝓞 F)) : AEF F E := fj E (singleV F v 1)

theorem pl_mul_pl {v v' : HeightOneSpectrum (𝓞 F)} (h : v ≠ v') : pl E v * pl E v' = 0 := by
  have : singleV F v 1 * singleV F v' 1 = 0 := afext fun w => by
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw; rw [evalV_singleV_ne _ v' _ h, mul_zero]
    · rw [evalV_singleV_ne _ v _ hw, zero_mul]
  rw [← map_mul, this, map_zero]

theorem idem_eq_sum (e : Af F) (he : e * e = e) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∈ S ↔ evalV F v e ≠ 0) : e = ∑ v ∈ S, singleV F v 1 := by
  refine afext fun w => ?_
  rw [map_sum]
  by_cases hw : w ∈ S
  · rw [Finset.sum_eq_single w (fun v _ hv => evalV_singleV_ne _ v _ hv.symm) (fun h => absurd hw h),
      evalV_singleV_same]
    have h1 := congrArg (evalV F w) he
    rw [map_mul] at h1
    exact mul_left_cancel₀ ((hS w).1 hw) (h1.trans (mul_one _).symm)
  · rw [Finset.sum_eq_zero fun v hv => evalV_singleV_ne _ v _ (fun h : w = v => hw (h ▸ hv))]
    by_contra h
    exact hw ((hS w).2 h)

theorem exists_of_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) : ∃ t : F, algebraMap F E t = x := by
  obtain ⟨θ, d, hd, h1, h2, h3⟩ := GlobalTheory.SplitDetCharF.exists_int_basis h
  obtain ⟨u, w, rfl⟩ := h3 x
  have hθ : θ ≠ 0 := fun h0 => hd ((algebraMap F E).injective (by rw [← h2, h0, mul_zero, map_zero]))
  simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, h1, add_right_inj] at hx
  rw [← Algebra.smul_def, ← Algebra.smul_def, smul_neg] at hx
  have hw : w • θ = 0 := by
    have : (2 : E) * (w • θ) = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact ⟨u, by rw [hw, add_zero, Algebra.algebraMap_eq_smul_one]⟩

theorem exists_int {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : 𝓞 E) (hx : σ (x : E) = x) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t = x ∧ algebraMap F E (t : F) = x := by
  obtain ⟨t, ht⟩ := exists_of_fixed h hx
  have hi : IsIntegral ℤ t := (isIntegral_algebraMap_iff (algebraMap F E).injective).1 (ht ▸ x.2)
  exact ⟨⟨t, hi⟩, RingOfIntegers.ext ht, ht⟩

theorem exists_splitAt {c : E ≃ₐ[F] E} (h : IsCMExt F E (c : E →ₐ[F] E)) (v : HeightOneSpectrum (𝓞 F))
    (hv : SplitPl c v) : ∃ e : AEF F E, IsSplitIdemF (c : E →ₐ[F] E) e ∧ e + cAF (c : E →ₐ[F] E) e = pl E v := by
  obtain ⟨P, hP, hPv, a, ha, b, hb, hbP⟩ := hv
  have hcc : ∀ x, c (c x) = x := GlobalTheory.SplitDetCharF.sig_invol h
  obtain ⟨t, ht, ht'⟩ := exists_int h (a + b) (by
    show c ((a : E) + b) = (a : E) + b
    rw [hb, map_add, hcc, add_comm])
  obtain ⟨n, hn, hn'⟩ := exists_int h (a * b) (by
    show c ((a : E) * b) = (a : E) * b
    rw [hb, map_mul, hcc, mul_comm])
  have htv : t ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, ht]
    exact fun h => hbP ((Ideal.add_mem_iff_right P ha).1 h)
  have hnv : n ∈ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, hn]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨r, u, hr, hu⟩ := GlobalTheory.MovedSplit.exists_root F v t n htv hnv
  have key := GlobalTheory.MovedSplit.idem_tensor (placeHom F v) (fun s y => by
      refine Prod.ext (mul_zero _).symm ?_
      show singleV F v _ = algebraMap F (Af F) s * singleV F v y
      rw [singleV_mul, AlgHom.commutes])
    (cAF (c : E →ₐ[F] E)) (a : E) (b : E) (t : F) (n : F) (r : Fv F v) (u : Fv F v)
    (fun x => by rw [cA_tmul, map_one]) (fun x => by rw [cA_tmul, hb]; rfl) ht' hn'
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, ⟨key.1, key.2.1, v, _, ⟨_, rfl, evalV_singleV_same _ v 1, fun w hw => evalV_singleV_ne _ v _ hw⟩, key.2.2⟩,
    key.2.2⟩

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def cutA (ε : AEF F E) (hε : ε * ε = ε) (hσ : cAF σ ε = ε) : GAF σ J →* GAF σ J :=
  cutH (AF F) σ J ε hε hσ

theorem mt_cutA (ε : AEF F E) (hε : ε * ε = ε) (hσ : cAF σ ε = ε) (g : GAF σ J) :
    mtF σ J (cutA σ J ε hε hσ g) = 1 + ε • (mtF σ J g - 1) := cut_val _ _ ε hε hσ g

theorem mt_ext {g h : GAF σ J} (e : mtF σ J g = mtF σ J h) : g = h := Subtype.ext (Units.ext e)

theorem mt_mul (g h : GAF σ J) : mtF σ J (g * h) = mtF σ J g * mtF σ J h := rfl

theorem cutA_mul (ε : AEF F E) (hε : ε * ε = ε) (hσ : cAF σ ε = ε)
    (hε' : (1 - ε) * (1 - ε) = 1 - ε) (hσ' : cAF σ (1 - ε) = 1 - ε) (g : GAF σ J) :
    cutA σ J ε hε hσ g * cutA σ J (1 - ε) hε' hσ' g = g :=
  mt_ext (GlobalTheory.UnRep.SplitRep.mix_mul_mix ε hε hε' (matHomF σ J g))

theorem inf_fj (e : Af F) : infPartF F E (fj E e) = 0 := TensorProduct.zero_tmul _ _

theorem fin_fj (e : Af F) : finPartF F E (fj E e) = e ⊗ₜ[F] 1 := rfl

theorem idem_inf : (1 - fj E (1 : Af F)) * (1 - fj E 1) = 1 - fj E 1 := by
  have : fj E (1 : Af F) * fj E 1 = fj E 1 := by rw [← map_mul, mul_one]
  linear_combination this

theorem conj_inf : cAF σ (1 - fj E (1 : Af F)) = 1 - fj E 1 := by rw [map_sub, map_one, cA_fj]

variable (σ J) in

def pInf : GAF σ J →* GAF σ J := cutA σ J (1 - fj E 1) idem_inf conj_inf

theorem inf_pInf (g : GAF σ J) : (mtF σ J (pInf σ J g)).map (infPartF F E) = (mtF σ J g).map (infPartF F E) := by
  rw [pInf, mt_cutA, map_cut, RingHom.map_sub, RingHom.map_one, inf_fj, sub_zero, one_smul, add_sub_cancel]

theorem fin_pInf (g : GAF σ J) : (mtF σ J (pInf σ J g)).map (finPartF F E) = 1 := by
  rw [pInf, mt_cutA, map_cut, RingHom.map_sub, RingHom.map_one, fin_fj, ← Algebra.TensorProduct.one_def, sub_self,
    zero_smul, add_zero]

theorem ga_ext {g h : GAF σ J} (h1 : (mtF σ J g).map (infPartF F E) = (mtF σ J h).map (infPartF F E))
    (h2 : (mtF σ J g).map (finPartF F E) = (mtF σ J h).map (finPartF F E)) : g = h :=
  mt_ext (Matrix.ext fun i j => parts_inj _ _ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j))

theorem continuous_cA : Continuous (cAF σ) := by
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul _ _
  exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toLinearMap

theorem inf_scal (e : Af F) (x : E) :
    infPartF F E (1 + (1 - fj E e) * (incAF F E x - 1)) = inclR (F := F) (Ainf F) x :=
  map_scal_zero (infPartF F E) (fj E e) (incAF F E x) (inf_fj e)

theorem fin_scal (e : Af F) (x : E) :
    finPartF F E (1 + (1 - fj E e) * (incAF F E x - 1)) = 1 + (1 - e) ⊗ₜ[F] (x - 1) :=
  (map_scal (finPartF F E) (fj E e) (incAF F E x)).trans (tmul_scal e x)

theorem tendsto_scal {w : ℕ → E} {u : E} {e : ℕ → Af F}
    (t1 : Tendsto (fun k => inclR (F := F) (Ainf F) (w k)) atTop (𝓝 (inclR (F := F) (Ainf F) u)))
    (t2 : Tendsto (fun k => ((1 - e k) ⊗ₜ[F] (w k - 1) : Af F ⊗[F] E)) atTop (𝓝 0)) :
    Tendsto (fun k => 1 + (1 - fj E (e k)) * (incAF F E (w k) - 1)) atTop
      (𝓝 (1 + (1 - fj E 1) * (incAF F E u - 1))) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  refine tendsto_AE ?_ ?_
  · rw [inf_scal 1 u, funext fun k => inf_scal (e k) (w k)]
    exact t1
  · rw [fin_scal 1 u, sub_self, TensorProduct.zero_tmul, funext fun k => fin_scal (e k) (w k)]
    exact t2.const_add 1

end PositivityTheory.ThKW.SplitChar

end
