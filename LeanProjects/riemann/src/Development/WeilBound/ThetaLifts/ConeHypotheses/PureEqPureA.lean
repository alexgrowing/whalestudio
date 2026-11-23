import Development.WeilBound.ThetaLifts.ConeHypotheses.PolDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.WeilBound.ThetaLifts.ConeHypotheses.IsLocallyConstantFinprodEvalV

noncomputable section

namespace PositivityTheory.ThKG

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) : ResEtaPow K (χ / χ') (n + m) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), pow_add, mul_assoc, hm, mul_one]

variable {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem pairV (t : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨t.base, t.geo.hV, t.geo.hW, t.geo.hM, t.chars.heckeβ, isHecke_div t.chars.heckeβ t.chars.heckeα, t.chars.resβ,
    resEtaPow_div t.chars.resβ t.chars.resα, t.weil⟩

theorem pairV' (t : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨t.base, t.geo.hV', t.geo.hW, t.geo.hM', t.chars.heckeα, isHecke_div t.chars.heckeα t.chars.heckeβ, t.chars.resα,
    by rw [add_comm a a']; exact resEtaPow_div t.chars.resα t.chars.resβ, t.weil'⟩

theorem weilCondV (t : IsTriple B G X om om') : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
  have := t.geo.eBig
  left
  omega

section Pair

variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_smul (M : Model σ Y W) (o : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) : M.I o (c • Φ) h = c * M.I o Φ h := by
  simp only [Model.I, theta, map_smul, thetaSum_smul, integral_const_mul]

theorem I_zero (M : Model σ Y W) (o : Rep σ Y W) : M.I o 0 = 0 := by
  funext h
  simp [Model.I, theta, thetaSum]

theorem I_add {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} (hw : M.IsWeil B.ψ χ χ' o)
    (hc : ∀ Φ ∈ schA F _, M.Conv o Φ) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (h : UA σ W.J) :
    M.I o (Φ + Ψ) h = M.I o Φ h + M.I o Ψ h := by
  have e : ∀ g, theta o (Φ + Ψ) g h = theta o Φ g h + theta o Ψ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (hw.isUSplitting.pres _ _ hΦ) (hw.isUSplitting.pres _ _ hΨ)
  simp only [Model.I, e]
  exact integral_add (hc _ hΦ h) (hc _ hΨ h)

theorem I_sum {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} (hw : M.IsWeil B.ψ χ χ' o)
    (hc : ∀ Φ ∈ schA F _, M.Conv o Φ) {ι : Type} (s : Finset ι) (Φ : ι → Fn F n d) (hΦ : ∀ i, Φ i ∈ schA F _) (h : UA σ W.J) :
    M.I o (∑ i ∈ s, Φ i) h = ∑ i ∈ s, M.I o (Φ i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [I_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, I_add hw hc (hΦ i) (Submodule.sum_mem _ fun j _ => hΦ j), ih]

theorem pureA_mem (f : SInf F (Fin n × Fin d)) {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) : pureA F f g ∈ schA F _ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem pure_eq_pureA {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ SB _) (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∃ g ∈ SB (Fin n × Fin d → Af F), ∀ f : SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = pureA F f g :=
  have h3 := (h2.and hM.std).mono fun _ h => h.1.trans h.2
  ⟨_, ⟨isLocallyConstant_finprod_evalV φ h1 h3, hasCompactSupport_finprod φ h1 h3⟩, fun _ => rfl⟩

theorem polData_le {M : Model σ Y W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  obtain ⟨g, hg, e⟩ := pure_eq_pureA hM φ h1 h2
  rw [e]
  exact pureA_mem f hg

theorem isLevi_one {d₁ : ℕ} {W₁ : Spc F E d₁} (H' : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 := by
  simp [IsLevi, mat]

end Pair

theorem split2_smul {W : Spc F E (a + a')} {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {f fa fb : UA σ W.J → ℂ}
    (h : Split2 W₁ H' X f fa fb) (c : ℂ) : Split2 W₁ H' X (c • f) (c • fa) (c • fb) := by
  refine ⟨fun μ 𝓕 h1 h2 h3 g => ?_, fun t m hm g => ?_, fun t m hm g => ?_⟩
  · have := h.1 μ 𝓕 h1 h2 h3 g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [integral_const_mul, ← this]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, h.2.1 t m hm g]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, h.2.2 t m hm g]; ring

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem polMatch_mem {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', h1, h2, rfl, rfl, -⟩ := h
  have cof : ∀ {P : Pl F → Prop}, (∀ v ∉ T, P v) → ∀ᶠ v in cofinite, P v := fun {P} hP =>
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (hP v h'))
  exact ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (h1 i).1, φ i, (h1 i).2.1, cof (h1 i).2.2, rfl⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, (h2 i).1, φ' i, (h2 i).2.1, cof (h2 i).2.2, rfl⟩⟩

end PositivityTheory.ThKG

end
