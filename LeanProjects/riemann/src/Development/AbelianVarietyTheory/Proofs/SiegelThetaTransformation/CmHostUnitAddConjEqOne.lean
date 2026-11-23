import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.MarkMove

open GlobalTheory.DatumInverseCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {r g n : ℕ}

theorem datum_move {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c n)
    (hM : d.l₂.M = l.M * d.pd) (hb : d.l₂.Mb = l.Mb * d.I) (ph : (Fin n → LaJ Xo c d) → c.F)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d) (hpin : d.PhiPin ph ψ x₀)
    (f g' : Dw.La →ₗ[𝓞 E] Dw.La)
    (hg' : ∀ a, Dw.ModN d.l₂.M (g' (f a) - a) ∧ Dw.ModN d.l₂.M (f (g' a) - a))
    (hf1 : ∀ a, f a - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂),
      (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a)) ∧
      ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂),
        d.w x0 (fun b => σq.symm (q b)) = d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.w x0 q := by
  obtain ⟨-, -, hc, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hspan : ∀ (l' : Geo.Tor.Level H), ((l'.M : ℕ) : 𝓞 E) ∈ l'.Mb * l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := fun l' => by
    rw [l'.prod]; exact Ideal.mem_span_singleton_self _
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := (Ideal.mul_le_inf.trans inf_le_left) (hspan d.l₂)
  have hmJ : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) :=
    Ideal.map_mono hbI ((Ideal.mul_le_inf.trans inf_le_right) (hspan d.l₂))
  obtain ⟨kI, hkI⟩ := exists_quot_equiv Dw (hbI hmb) f g' hg'
  obtain ⟨σ, hσ⟩ := exists_quot_equiv Dw hmb f g' hg'
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw f
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  obtain ⟨kst, hkst⟩ := exists_quot_equiv Dw hmJ fa ga (fun a => by
    constructor
    · refine modN_of_dvd Dw hM₂ fun v => ?_
      rw [map_sub, LinearMap.sub_apply, hga, hfa, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).2
    · refine modN_of_dvd Dw hM₂ fun v => ?_
      rw [map_sub, LinearMap.sub_apply, hfa, hga, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).1)
  have hcm := cHalf_mem (H := H) d.I
  have hA : ∀ u v : Dw.La, (d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
      Dw.EF u (cHalf H d.I • f v) := by
    intro u v
    have h1 : qRep (kst (Submodule.Quotient.mk u)) - fa u ∈
        (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
      rw [← Submodule.Quotient.eq, qRep_spec, hkst]
    have := dvd_left Dw hIJ hcm v h1
    rwa [map_sub, LinearMap.sub_apply, hfa, f.map_smul] at this
  have hB : ∀ u w w' : Dw.La, w - w' ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) →
      (d.pd : ℤ) ∣ Dw.EF u (cHalf H d.I • w) - Dw.EF u (cHalf H d.I • w') := by
    intro u w w' h
    have := dvd_right Dw hIJ hcm u h
    rwa [smul_sub, map_sub] at this
  have hph := hc kI kst (fun u v => by
    have h1 := hA u v
    have h2 := hB u (f v) (qRep (kI (Submodule.Quotient.mk v))) (by
      rw [← Submodule.Quotient.eq, qRep_spec, hkI])
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this)
  refine ⟨kI, σ.toEquiv, hσ, fun x0 q => ?_⟩
  have hq : ∀ b, f (levRep (σ.toEquiv.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x0 (fun b => levRep (σ.toEquiv.symm (q b))) =
      zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw l.prod (cSep_mem l) _ ?_
    set a := levRep (σ.toEquiv.symm (q b))
    have h1 : f a - levRep (q b) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mono hbM le_rfl (hq b)
    have := sub_mem h1 (hf1 a)
    convert this using 1
    abel
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.toEquiv.symm (q b))) =
      d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (d.φδ q) := by
    rw [hφ, hφ, ← smul_eq_mul, smul_finsum,
      ← finsum_comp_equiv (Equiv.piCongrRight (fun _ : Fin n => kst.toEquiv))]
    refine finsum_congr fun x => ?_
    change d.eF (ph (fun b => kst (x b))) * _ ^ (∑ b, Dw.EF (qRep (kst (x b))) _) = _
    rw [hph, map_mul, smul_eq_mul, _root_.mul_assoc]
    congr 2
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    have h1 := hA (qRep (x b)) (levRep (σ.toEquiv.symm (q b)))
    rw [qRep_spec] at h1
    have h2 := hB (qRep (x b)) _ _ (Submodule.smul_mono hbI le_rfl (hq b))
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]
  ring

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem cSep_spec (l : Geo.Tor.Level H) : cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by
      unfold Mfr; rw [l.coprime]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, hb, ?_⟩
    rw [← hab]
    simpa using ha
  unfold cSep
  rw [dif_pos h]
  exact h.choose_spec

theorem level_mem (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb ∧ (l.M : 𝓞 E) ∈ Mfr l := by
  have : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    unfold Mfr; rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact ⟨(Ideal.mul_le_inf.trans inf_le_left) this, (Ideal.mul_le_inf.trans inf_le_right) this⟩

theorem modN_smul (l : Geo.Tor.Level H) {I J : Ideal (𝓞 E)} (hIJ : I * J = Ideal.span {(l.M : 𝓞 E)})
    {t : 𝓞 E} (ht : t ∈ I) {a : Dw.La} (ha : a ∈ (J • ⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ b, t • a = l.M • b := by
  have h : t • a ∈ ((Ideal.span {(l.M : 𝓞 E)}) • ⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← hIJ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul ht ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, -, hb⟩ := h
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem modN_of_both (l : Geo.Tor.Level H) {a : Dw.La} (h1 : a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La))
    (h2 : a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) : ∃ b, a = l.M • b := by
  obtain ⟨b, hb⟩ := modN_smul l l.prod (cSep_spec l).2 h1
  obtain ⟨b', hb'⟩ := modN_smul l ((mul_comm _ _).trans l.prod) (cSep_spec l).1 h2
  refine ⟨b' - b, ?_⟩
  rw [smul_sub, ← hb, ← hb', sub_smul, one_smul, sub_sub_cancel]

theorem exists_comp (l : Geo.Tor.Level H) {L : Lt E r} {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : IsMark l L mk) (h' : IsMark l L mk') :
    ∃ f : Dw.La →ₗ[𝓞 E] Dw.La, (∀ a, f a - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) ∧
      ∀ a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' (f a) + l.M • u := by
  haveI := Dw.proj
  set P : Submodule (𝓞 E) Dw.La := Mfr l • ⊤ with hP
  set K : Submodule (𝓞 E) (Fin r → E) := L.map (LinearMap.lsmul (𝓞 E) (Fin r → E) (l.M : 𝓞 E)) with hK
  have hKm : ∀ v, v ∈ K ↔ ∃ u ∈ L, v = l.M • u := fun v => by
    simp only [hK, Submodule.mem_map, LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, eq_comm]
  let G : P →ₗ[𝓞 E] ((Fin r → E) ⧸ K) := K.mkQ ∘ₗ mk' ∘ₗ P.subtype
  let F : Dw.La →ₗ[𝓞 E] ((Fin r → E) ⧸ K) := cSep l • (K.mkQ ∘ₗ mk)
  have hF : ∀ a, F a ∈ LinearMap.range G := fun a => by
    obtain ⟨a', ha', u, hu, e⟩ := h'.surj (cSep l • mk a) (Submodule.smul_mem_smul (cSep_spec l).1 (h.mem a))
    refine ⟨⟨a', ha'⟩, ?_⟩
    change K.mkQ (mk' a') = cSep l • K.mkQ (mk a)
    rw [← map_smul, e, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hKm _).2 ⟨-u, neg_mem hu, by simp⟩
  obtain ⟨f0, hf0⟩ := Module.projective_lifting_property G.rangeRestrict (F.codRestrict _ hF)
    G.surjective_rangeRestrict
  have hf : ∀ a, ∃ u ∈ L, mk' (f0 a) - cSep l • mk a = l.M • u := fun a => by
    have : G (f0 a) = F a := congrArg Subtype.val (LinearMap.congr_fun hf0 a)
    change K.mkQ (mk' (f0 a)) = cSep l • K.mkQ (mk a) at this
    rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at this
    exact (hKm _).1 this
  refine ⟨P.subtype ∘ₗ f0 - (cSep l - 1) • LinearMap.id, fun a => ?_, fun a ha => ?_⟩
  · have : ((P.subtype ∘ₗ f0 - (cSep l - 1) • LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) - a =
        (f0 a : Dw.La) - cSep l • a := by
      simp [sub_smul]; abel
    rw [this]
    exact sub_mem (f0 a).2 (Submodule.smul_mem_smul (cSep_spec l).1 trivial)
  · obtain ⟨u, hu, e⟩ := hf a
    obtain ⟨b, hb⟩ := modN_smul l l.prod (cSep_spec l).2 ha
    refine ⟨-u + (mk' b - mk b), add_mem (neg_mem hu) (sub_mem (h'.mem b) (h.mem b)), ?_⟩
    change mk a = mk' ((f0 a : Dw.La) - (cSep l - 1) • a) + _
    have e2 : cSep l • mk a - mk a = l.M • mk b := by
      rw [← map_nsmul, ← hb, map_smul, sub_smul, one_smul]
    rw [hb, map_sub, map_nsmul, smul_add, smul_neg, smul_sub, ← e, ← e2]
    abel

theorem comp_inv (l : Geo.Tor.Level H) {L : Lt E r} {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : IsMark l L mk) {f f' : Dw.La →ₗ[𝓞 E] Dw.La}
    (h1 : ∀ a, f a - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La))
    (h2 : ∀ a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' (f a) + l.M • u)
    (h1' : ∀ a, f' a - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La))
    (h2' : ∀ a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk (f' a) + l.M • u) (a : Dw.La) :
    Dw.ModN l.M (f' (f a) - a) := by
  have hm : ∀ a, f' (f a) - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
    have := add_mem (h1' (f a)) (h1 a)
    rwa [sub_add_sub_cancel] at this
  have hc : cSep l • a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul (cSep_spec l).1 trivial
  obtain ⟨u, hu, e⟩ := h2 _ hc
  obtain ⟨u', hu', e'⟩ := h2' (f (cSep l • a)) (by
    rw [map_smul]; exact Submodule.smul_mem_smul (cSep_spec l).1 trivial)
  obtain ⟨b, hb⟩ := h.inj _ (hm (cSep l • a)) ⟨-(u + u'), neg_mem (add_mem hu hu'), by
    rw [map_sub, e, e', smul_neg, smul_add]; abel⟩
  obtain ⟨b', hb'⟩ := modN_smul l l.prod (cSep_spec l).2 (hm a)
  refine ⟨b - b', ?_⟩
  rw [smul_sub, ← hb, ← hb', map_smul, map_smul, ← smul_sub, sub_smul, one_smul, sub_sub_cancel]

theorem comp_base {l l₂ : Geo.Tor.Level H} (hd : l.Dvd l₂) {L : Lt E r} {mk mk₂ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : IsMark l L mk) (o₂ : MarkOver l l₂ L mk mk₂) (o₃ : MarkOver l l₂ L mk mk₃) {f : Dw.La →ₗ[𝓞 E] Dw.La}
    (h2 : ∀ a ∈ (Mfr l₂ • ⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk₂ a = mk₃ (f a) + l₂.M • u) (a : Dw.La) :
    f a - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨⟨k, hk⟩, hb, -⟩ := hd
  have hc : ∀ a : Dw.La, cSep l₂ • a ∈ (Mfr l₂ • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    Submodule.smul_mem_smul (cSep_spec l₂).1 trivial
  obtain ⟨u, hu, e⟩ := h2 _ (hc a)
  obtain ⟨u₂, hu₂, e₂⟩ := o₂ _ (hc a)
  obtain ⟨u₃, hu₃, e₃⟩ := o₃ _ (hc (f a))
  rw [map_smul f, e₂, e₃, hk, mul_smul] at e
  obtain ⟨b, hb'⟩ := h.inj (cSep l₂ • (f a - a))
    (Submodule.smul_mem_smul (Ideal.map_mono hb (cSep_spec l₂).1) trivial)
    ⟨u₂ - u₃ - k • u, sub_mem (sub_mem hu₂ hu₃) (nsmul_mem hu k), by
      rw [smul_sub, map_sub, smul_sub, smul_sub, eq_sub_of_add_eq e]; abel⟩
  have : f a - a = l.M • b - (cSep l₂ - 1) • (f a - a) := by
    rw [← hb', sub_smul, one_smul, sub_sub_cancel]
  rw [this, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact sub_mem (Submodule.smul_mem_smul (level_mem l).1 trivial)
    (Submodule.smul_mem_smul (hb (cSep_spec l₂).2) trivial)

theorem mem_of_coprime {G : Type} [AddCommGroup G] (A : AddSubgroup G) {a b : ℕ} (hab : a.Coprime b) {x : G}
    (ha : a • x ∈ A) (hb : b • x ∈ A) : x ∈ A := by
  obtain ⟨s, t, e⟩ := Nat.isCoprime_iff_coprime.2 hab
  have : x = s • a • x + t • b • x := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, e, one_smul]
  rw [this]
  exact add_mem (zsmul_mem ha s) (zsmul_mem hb t)

theorem row_half (l : Geo.Tor.Level H) {L : Lt E r} {N : ℕ} (hN : l.M ∣ N) {y y' : Fin r → E} (hL : y - y' ∈ L)
    (hy : ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • y = (2 * N) • u)
    (hy' : ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • y' = (2 * N) • u) :
    ∃ u ∈ Mfr l • L, y = y' + (u + u) ∧ ∃ j : ℕ, ∃ u' ∈ L, l.M ^ j • u = N • u' := by
  obtain ⟨j, hj⟩ := hy
  obtain ⟨j', hj'⟩ := hy'
  set u : Fin r → E := (2⁻¹ : E) • (y - y') with hu
  have huu : u + u = y - y' := by rw [hu, ← add_smul]; norm_num
  have key : ∀ s ∈ l.Mb ^ (j + j'), ∃ u' ∈ L, s • u = N • u' := fun s hs => by
    obtain ⟨a, ha, e⟩ := hj s (Ideal.pow_le_pow_right (Nat.le_add_right _ _) hs)
    obtain ⟨a', ha', e'⟩ := hj' s (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hs)
    refine ⟨a - a', sub_mem ha ha', ?_⟩
    rw [hu, smul_comm, smul_sub, e, e', ← smul_sub, ← Nat.cast_smul_eq_nsmul E, smul_smul,
      ← Nat.cast_smul_eq_nsmul E]
    congr 1
    push_cast
    field_simp
  obtain ⟨u', hu', e⟩ := key _ (Ideal.pow_mem_pow (level_mem l).1 _)
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at e
  have huL : u ∈ L := by
    refine mem_of_coprime L.toAddSubgroup (a := 2) (b := l.M ^ (j + j'))
      (Nat.Coprime.pow_right _ (Nat.coprime_two_left.2 l.odd)) ?_ ?_
    · rw [two_nsmul, huu]; exact hL
    · rw [e]; exact nsmul_mem hu' _
  refine ⟨u, ?_, by rw [huu]; abel, j + j', u', hu', e⟩
  have h1 : 1 - cSep l ∈ l.Mb := by simpa using neg_mem (cSep_spec l).2
  obtain ⟨a, ha, e1⟩ := key _ (Ideal.pow_mem_pow h1 _)
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (1 : 𝓞 E) (1 - cSep l) (j + j')
  obtain ⟨k, rfl⟩ := hN
  have : u = (cSep l * t) • u + (l.M : 𝓞 E) • (k • a) := by
    rw [Nat.cast_smul_eq_nsmul, ← mul_smul, ← e1, ← add_smul]
    rw [one_pow, sub_sub_cancel] at ht
    rw [← ht, sub_add_cancel, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_right _ _ (cSep_spec l).1) huL)
    (Submodule.smul_mem_smul (level_mem l).2 (nsmul_mem ha k))

theorem EF_int (l : Geo.Tor.Level H) {X : Data E r} {L : Lt E r} (hL : SelfD X L) {y u : Fin r → E}
    (hy : ∀ t ∈ l.Mb, t • y ∈ L) (hu : u ∈ Mfr l • L) : ∃ k : ℤ, EF X y u = k := by
  refine Submodule.smul_induction_on hu (fun m hm x hx => ?_) fun x x' ⟨k, hk⟩ ⟨k', hk'⟩ => ?_
  · obtain ⟨k, hk⟩ := (hL.2 _).1 (hy _ (bar_mem hm)) x hx
    refine ⟨k, ?_⟩
    rw [← hk]
    change EF X y ((m : E) • x) = EF X (((H.bar m : 𝓞 E) : E) • y) x
    rw [TensLat.EF_smul, H.bar_eq, cc, IsCMField.complexConj_apply_apply]
  · exact ⟨k + k', by rw [TensLat.EF_eq_bilin, map_add, ← TensLat.EF_eq_bilin, ← TensLat.EF_eq_bilin, hk, hk',
      Int.cast_add]⟩

theorem mem_tens {Λ : Lt E n} {L : Lt E r} {M N : ℕ} (hΛ : Λ ∈ Vset E n M) (hN : NOK Λ N M)
    {u : Matrix (Fin n) (Fin r) E} (hu : ∀ b, u b ∈ L ∧ ∃ j : ℕ, ∃ u' ∈ L, M ^ j • u b = N • u') :
    u ∈ tens Λ L := by
  have e : u = ∑ b, vecMulVec (Pi.single b (1 : E)) (u b) := by
    ext i j
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  rw [e]
  refine AddSubgroup.sum_mem _ fun b _ => ?_
  obtain ⟨hb, j, u', hu', h⟩ := hu b
  obtain ⟨s, -, hs, -, hs'⟩ := hΛ.2.2
  refine mem_of_coprime _ (hs.pow_right j) ?_ ?_
  · refine AddSubgroup.subset_closure ⟨_, hs' (Pi.single b 1) (Submodule.subset_span ⟨b, rfl⟩), _, hb, ?_⟩
    ext i k
    simp [vecMulVec_apply, _root_.mul_assoc]
  · have h1 : (N : 𝓞 E) • (Pi.single b 1 : Fin n → E) ∈ Λ :=
      (hN.2.2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (fun i _ => by
        by_cases hi : i = b
        · subst hi; simpa using Submodule.one_le.1 le_rfl
        · simp [hi]))).1
    refine AddSubgroup.subset_closure ⟨_, h1, _, hu', ?_⟩
    ext i k
    have := congrFun h k
    simp only [Pi.smul_apply, nsmul_eq_mul] at this
    rw [Nat.cast_smul_eq_nsmul]
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    linear_combination (Pi.single b 1 : Fin n → E) i * this

theorem heis_eq {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r}
    (hL : SelfD X L) {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {v : TF n g} (hv : IsVac X bas w (tens Λ L) v)
    {y u : Matrix (Fin n) (Fin r) E} (hu : u ∈ tens Λ L) (hy : ∀ b, ∃ k : ℤ, EF X (y b) (u b) = k) :
    heisG X bas (y + (u + u)) v = heisG X bas y v := by
  have hsc := (TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw' L hL M Λ hΛ).2.2.1 u hu
  have h0 : ∀ b, EF X (u b) (u b) = 0 := fun b => by
    have := TensLat.EF_swap X (u b) (u b)
    linarith
  have h1 : epsW X w (u + u) = 1 := by
    rw [hsc.2 u hu, ← sq, hsc.1]
    simp [h0]
  have h2 := hv.2.2 (u + u) (add_mem hu hu)
  rw [h1, one_smul] at h2
  have h3 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 y v hv.1).2.2.1 (u + u)
  rw [h2] at h3
  choose k hk using hy
  have h4 : (∑ b, EF X (y b) ((u + u) b)) = 2 * ((∑ b, k b : ℤ) : ℚ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    change EF X (y b) (u b + u b) = _
    rw [TensLat.EF_eq_bilin, map_add, ← TensLat.EF_eq_bilin, hk, two_mul]
  have h5 := Complex.exp_int_mul_two_pi_mul_I (-(∑ b, k b))
  rw [h3, h4]
  have h6 : -((Real.pi : ℂ) * I * ((2 * ((∑ b, k b : ℤ) : ℚ) : ℚ) : ℂ)) =
      ((-(∑ b, k b) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [h6, h5, one_smul]

theorem root_mem (l : Geo.Tor.Level H) {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : IsMark l L mk)
    {a : Dw.La} (ha : a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) {y : Fin r → E}
    (hy : y - ((l.M : E)⁻¹) • mk a ∈ L) {t : 𝓞 E} (ht : t ∈ l.Mb) : t • y ∈ L := by
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  obtain ⟨b, hb⟩ := modN_smul l l.prod ht ha
  have : t • y = t • (y - ((l.M : E)⁻¹) • mk a) + mk b := by
    rw [smul_sub, smul_comm t, ← map_smul, hb, map_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
      inv_mul_cancel₀ hM, one_smul, sub_add_cancel]
  rw [this]
  exact add_mem (L.smul_mem _ hy) (h.mem b)

theorem finite_half {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c n)
    (hb : d.l₂.Mb = l.Mb * d.I) : Finite (LaI Xo c d) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LaI Xo c d) := Module.Finite.trans (𝓞 E) _
  have hM : (d.l₂.M : 𝓞 E) ∈ d.I := (Ideal.mul_le_inf.trans inf_le_right) (hb ▸ (level_mem d.l₂).1)
  refine Module.finite_of_fg_torsion _ fun q => ⟨⟨(d.l₂.M : ℤ), mem_nonZeroDivisors_of_ne_zero (by
    have := d.l₂.three_le; omega)⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change (d.l₂.M : ℤ) • (Submodule.Quotient.mk a : LaI Xo c d) = 0
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hM trivial

theorem gphi_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ], d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) , IsSympl X bas → Even n → r = Dw.p + Dw.q → r ≤ n → ∀ L : Lt E r, SelfD X L → ∀ mk mk₂ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → IsMark d.l₂ L mk₂ → IsMark d.l₂ L mk₃ → MarkOver l d.l₂ L mk mk₂ → MarkOver l d.l₂ L mk mk₃ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x0 : Fin n → Dw.La) (v : TF n g), IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → ∀ Λ ∈ Vset E n d.l₂.M, ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y Y' : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → IsRoots d.l₂ L mk₃ N Y' → gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = t • gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y' := by
  intro E _ _ _ H Dw l Xo c n d _ hlev ph ψ x₀ hpin r g X bas idx hs hn _ _ L hL mk mk₂ mk₃ hm hm₂ hm₃ o₂ o₃
  obtain ⟨hd, hM, -, hb, -⟩ := hlev
  obtain ⟨f, hf1, hf2⟩ := exists_comp d.l₂ hm₂ hm₃
  obtain ⟨f', hf1', hf2'⟩ := exists_comp d.l₂ hm₃ hm₂
  obtain ⟨kI, σ, hσ, hw⟩ := datum_move d hM hb ph ψ x₀ hpin f f'
    (fun a => ⟨comp_inv d.l₂ hm₂ hf1 hf2 hf1' hf2' a, comp_inv d.l₂ hm₃ hf1' hf2' hf1 hf2 a⟩)
    (comp_base hd hm o₂ o₃ hf2)
  have hM0 : (d.l₂.M : E) ≠ 0 := by have := d.l₂.three_le; exact_mod_cast (by omega : d.l₂.M ≠ 0)
  refine ⟨algebraMap d.c₂.F ℂ (d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F)), ?_, ?_⟩
  · haveI := finite_half d hb
    haveI : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) := Finite.of_injective _ DFunLike.coe_injective
    obtain ⟨m, hm0, hm1⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite kI)
    refine Complex.norm_eq_one_of_pow_eq_one (n := m) ?_ hm0.ne'
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, hm1, map_one, inv_one,
      Units.val_one, map_one, map_one]
  intro x0 v hv Λ hΛ N hN Y Y' hY hY'
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.2
  have hwt : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    have := congrArg (fun x : 𝓞 E => (x : E)) (cmHostUnit_add_conj_eq_one H)
    rw [cc, ← H.bar_eq]
    simpa using this
  obtain ⟨⟨v₀, hv₀⟩, -, hp, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hwt L hL _ Λ hΛ
  have hYY : ∀ q, heisG X bas (Y q) v₀ = heisG X bas (Y' fun b => σ (q b)) v₀ := fun q => by
    have hrow : ∀ b, ∃ u, Y q b = Y' (fun b => σ (q b)) b + (u + u) ∧
        (u ∈ L ∧ ∃ j : ℕ, ∃ u' ∈ L, d.l₂.M ^ j • u = N • u') ∧
        ∃ k : ℤ, EF X (Y' (fun b => σ (q b)) b) u = k := fun b => by
      obtain ⟨⟨a, ha, e, h⟩, hj⟩ := hY q b
      obtain ⟨⟨a', ha', e', h'⟩, hj'⟩ := hY' (fun b => σ (q b)) b
      have hfa : f a ∈ (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La) := by
        simpa using add_mem (hf1 a) ha
      rw [← e, hσ, Submodule.Quotient.eq] at e'
      obtain ⟨z, hz⟩ := modN_of_both d.l₂ (sub_mem ha' hfa) e'
      obtain ⟨u, hu, e2⟩ := hf2 a ha
      have hdiff : Y q b - Y' (fun b => σ (q b)) b ∈ L := by
        have h3 := add_mem (sub_mem h h') (sub_mem hu (hm₃.mem z))
        convert h3 using 1
        rw [e2, eq_add_of_sub_eq' hz, map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul E,
          ← Nat.cast_smul_eq_nsmul E, smul_add, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hM0,
          one_smul, one_smul]
        abel
      obtain ⟨u₁, hu₁, e3, hj₁⟩ := row_half d.l₂ hN.2.1 hdiff hj hj'
      exact ⟨u₁, e3, ⟨Submodule.smul_le_right hu₁, hj₁⟩,
        EF_int d.l₂ hL (fun t ht => root_mem d.l₂ hm₃ ha' h' ht) hu₁⟩
    choose u hu1 hu2 hu3 using hrow
    have e : Y q = Y' (fun b => σ (q b)) + (Matrix.of u + Matrix.of u) := by
      funext b; exact hu1 b
    rw [e]
    exact heis_eq idx hs hn hwi hwt hL hΛ hv₀ (mem_tens hΛ hN hu2) hu3
  unfold gphi
  rw [hp v hv.1 v₀ hv₀, smul_finsum, ← finsum_comp_equiv (Equiv.piCongrRight (fun _ : Fin n => σ.symm))]
  refine finsum_congr fun q => ?_
  change algebraMap d.c₂.F ℂ (d.w x0 (fun b => σ.symm (q b))) • heisG X bas (Y fun b => σ.symm (q b)) _ = _
  rw [hw, map_mul, mul_smul, TensVac.heisG_smul, TensVac.heisG_smul, hYY]
  simp only [Equiv.apply_symm_apply]

end GlobalTheory.Dict.MarkMove
