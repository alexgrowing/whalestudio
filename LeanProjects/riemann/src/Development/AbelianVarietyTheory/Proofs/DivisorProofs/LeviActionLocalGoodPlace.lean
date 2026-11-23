import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.JacquetLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Groups

variable {n : ℕ} {X : Spc F E n}

theorem mat_mul (g h : UA σ X.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : UA σ X.J) = 1 := rfl

theorem mat_inv_mul (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1

theorem mat_mul_inv (g : UA σ X.J) : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1

theorem one_mem_UAt (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
  intro c _
  rw [mat_one, sub_self, smul_zero]

theorem mul_mem_UAt {v : Pl F} {g h : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) (hh : h ∈ UAt σ X (evFin F v)) :
    g * h ∈ UAt σ X (evFin F v) := by
  intro c hc
  have e : mat (g * h) - 1 = mat g * (mat h - 1) + (mat g - 1) := by
    rw [mat_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh c hc, hg c hc, Matrix.mul_zero, add_zero]

theorem conj_mem_UAt {v : Pl F} (g : UA σ X.J) {u : UA σ X.J} (hu : u ∈ UAt σ X (evFin F v)) :
    g * u * g⁻¹ ∈ UAt σ X (evFin F v) := by
  intro c hc
  have e : mat (g * u * g⁻¹) - 1 = mat g * (mat u - 1) * mat g⁻¹ := by
    rw [mat_mul, mat_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mat_mul_inv]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]

end Groups

theorem conj_mem_unip {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {t : (AE F E)ˣ}
    {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H' t 1 m) {u : UA σ W.J} (hu : u ∈ unip σ W H') :
    m * u * m⁻¹ ∈ unip σ W H' := by
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι with hιdef
  have hx : mat m *ᵥ x = (t : AE F E) • x := hm.1
  have hι : mat m * ι = ι := by
    have h := hm.2.2
    rw [mat_one, Matrix.mul_one] at h
    exact h
  have hx' : mat m⁻¹ *ᵥ x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • x := by
    have h1 : mat m⁻¹ *ᵥ (mat m *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [hx, Matrix.mulVec_smul] at h1
    calc mat m⁻¹ *ᵥ x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • ((t : AE F E) • mat m⁻¹ *ᵥ x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [h1]
  have hι' : mat m⁻¹ * ι = ι := by
    calc mat m⁻¹ * ι = mat m⁻¹ * (mat m * ι) := by rw [hι]
      _ = ι := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  have gen : ∀ w : UA σ W.J, (mat w *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat w *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x) →
      (mat (m * w * m⁻¹) *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat (m * w * m⁻¹) *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x) := by
    rintro w ⟨h1, h2⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [mat_mul, mat_mul]
      simp only [← Matrix.mulVec_mulVec]
      rw [hx', Matrix.mulVec_smul, h1, Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul]
    · obtain ⟨b, hb⟩ := h2 z
      refine ⟨b * t, ?_⟩
      have e1 : mat m⁻¹ *ᵥ (ι *ᵥ z) = ι *ᵥ z := by rw [Matrix.mulVec_mulVec, hι']
      have e2 : mat m *ᵥ (ι *ᵥ z) = ι *ᵥ z := by rw [Matrix.mulVec_mulVec, hι]
      rw [mat_mul, mat_mul]
      simp only [← Matrix.mulVec_mulVec]
      rw [e1, hb, Matrix.mulVec_add, e2, Matrix.mulVec_smul, hx, smul_smul]
  have hle : unip σ W H' ≤ (unip σ W H').comap (MulAut.conj m).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun w hw => ?_
    show (MulAut.conj m) w ∈ unip σ W H'
    rw [MulAut.conj_apply]
    exact Subgroup.subset_closure (gen w hw)
  have := hle hu
  simpa [MulAut.conj_apply] using this

end GlobalTheory.JacquetLevi

namespace GlobalTheory.JacquetLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Local

variable {κ : Type} [Fintype κ]

theorem acts_lin (v : Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hψ : ψ ∈ SB (κ → Fv F v))
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T ψ ψ₁) (a b : ℂ) :
    Acts (evFin F v) T (a • φ + b • ψ) (a • φ₁ + b • ψ₁) := by
  have hs : a • φ + b • ψ ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e : tens (evFin F v) (a • φ + b • ψ) R = a • tens (evFin F v) φ R + b • tens (evFin F v) ψ R := by
    funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e' : tens (evFin F v) (a • φ₁ + b • ψ₁) R = a • tens (evFin F v) φ₁ R + b • tens (evFin F v) ψ₁ R := by
    funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have key : tens (evFin F v) χ R = tens (evFin F v) (a • φ₁ + b • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e']
  have hχe : χ = a • φ₁ + b • ψ₁ := by
    funext t
    have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

theorem acts_mul (v : Pl F) {T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)}
    (h₁ : ∀ Φ ∈ schA F κ, T₁ Φ ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (a : Acts (evFin F v) T₁ φ φ₁) (b : Acts (evFin F v) T₂ φ₁ φ₂) : Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, by rw [← a r hr]; exact h₁ _ hr.2⟩
  show T₂ (T₁ _) = _
  rw [a r hr, b r hr1]

end Local

section Core

variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem image_jacKer (om : Rep σ X W) (H' : Plane E d d₁) (v : Pl F)
    (hEx : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁)
    (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    {t : (AE F E)ˣ} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H' t 1 m) (hmv : m ∈ UAt σ W (evFin F v))
    {z : (Fin n × Fin d → Fv F v) → ℂ} (hz : z ∈ GlobalTheory.JacquetLine.jacKer om H' v) :
    ∃ z₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, m)) z z₁ ∧ z₁ ∈ GlobalTheory.JacquetLine.jacKer om H' v := by
  have ex : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ := fun g hg h hh φ hφ =>
    let ⟨φ₁, h1, _⟩ := hEx g hg h hh φ hφ
    ⟨φ₁, h1.1, h1.2⟩
  have uq : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ φ₂, φ₁ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (om (g, h)) φ φ₁ →
        φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (om (g, h)) φ φ₂ → φ₁ = φ₂ :=
    fun g hg h hh φ hφ φ₁ φ₂ h1 a1 h2 a2 => (hEx g hg h hh φ hφ).unique ⟨h1, a1⟩ ⟨h2, a2⟩
  have h1X := one_mem_UAt (σ := σ) (X := X) v
  have h1W := one_mem_UAt (σ := σ) (X := W) v
  have exT := ex 1 h1X m hmv
  have sub : ∀ {φ ψ φ₁ ψ₁}, φ ∈ SB (Fin n × Fin d → Fv F v) → ψ ∈ SB (Fin n × Fin d → Fv F v) →
      Acts (evFin F v) (om (1, m)) φ φ₁ → Acts (evFin F v) (om (1, m)) ψ ψ₁ →
      Acts (evFin F v) (om (1, m)) (φ - ψ) (φ₁ - ψ₁) := fun hφ hψ a b => by
    simpa only [one_smul, neg_one_smul, ← sub_eq_add_neg] using acts_lin v _ exT hφ hψ a b 1 (-1)
  have add : ∀ {φ ψ φ₁ ψ₁}, φ ∈ SB (Fin n × Fin d → Fv F v) → ψ ∈ SB (Fin n × Fin d → Fv F v) →
      Acts (evFin F v) (om (1, m)) φ φ₁ → Acts (evFin F v) (om (1, m)) ψ ψ₁ →
      Acts (evFin F v) (om (1, m)) (φ + ψ) (φ₁ + ψ₁) := fun hφ hψ a b => by
    simpa only [one_smul] using acts_lin v _ exT hφ hψ a b 1 1
  have smul : ∀ (c : ℂ) {φ φ₁}, φ ∈ SB (Fin n × Fin d → Fv F v) →
      Acts (evFin F v) (om (1, m)) φ φ₁ → Acts (evFin F v) (om (1, m)) (c • φ) (c • φ₁) := fun c φ φ₁ hφ a => by
    simpa only [zero_smul, add_zero] using acts_lin v _ exT hφ hφ a a c 0
  have augSB : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt, Submodule.span_le]
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact sub_mem hφ₁ hφ
  have unSB : GlobalTheory.JacquetLine.unipAug om H' v ≤ SB (Fin n × Fin d → Fv F v) := by
    rw [GlobalTheory.JacquetLine.unipAug, Submodule.span_le]
    rintro _ ⟨u, -, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact sub_mem hφ₁ hφ
  have jSB : GlobalTheory.JacquetLine.jacKer om H' v ≤ SB (Fin n × Fin d → Fv F v) := sup_le augSB unSB
  suffices key : z ∈ SB (Fin n × Fin d → Fv F v) ∧
      ∃ z₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, m)) z z₁ ∧ z₁ ∈ GlobalTheory.JacquetLine.jacKer om H' v from key.2
  rw [GlobalTheory.JacquetLine.jacKer, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt, GlobalTheory.JacquetLine.unipAug, ← Submodule.span_union] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨g, hg, φ, hφ, φ₁, hφ₁, hact, rfl⟩ | ⟨u, hu, huv, φ, hφ, φ₁, hφ₁, hact, rfl⟩
    · obtain ⟨χ, hχ, aχ⟩ := exT φ hφ
      obtain ⟨χ₁, hχ₁, aχ₁⟩ := exT φ₁ hφ₁
      obtain ⟨χ', hχ', aχ'⟩ := ex g hg 1 h1W χ hχ
      have c1 : Acts (evFin F v) (om (g, m)) φ χ₁ := by
        have := acts_mul v (hpres _) hact aχ₁
        rwa [← map_mul, Prod.mk_mul_mk, one_mul, mul_one] at this
      have c2 : Acts (evFin F v) (om (g, m)) φ χ' := by
        have := acts_mul v (hpres _) aχ aχ'
        rwa [← map_mul, Prod.mk_mul_mk, one_mul, mul_one] at this
      have e := uq g hg m hmv φ hφ χ₁ χ' hχ₁ c1 hχ' c2
      refine ⟨sub_mem hφ₁ hφ, χ₁ - χ, sub_mem hχ₁ hχ, sub hφ₁ hφ aχ₁ aχ, ?_⟩
      refine GlobalTheory.JacquetLine.augAt_le_jacKer om H' v (Submodule.subset_span ⟨g, hg, χ, hχ, χ₁, hχ₁, ?_, rfl⟩)
      rw [e]; exact aχ'
    · obtain ⟨χ, hχ, aχ⟩ := exT φ hφ
      obtain ⟨χ₁, hχ₁, aχ₁⟩ := exT φ₁ hφ₁
      have hu' := conj_mem_UAt (v := v) m huv
      obtain ⟨χ', hχ', aχ'⟩ := ex 1 h1X _ hu' χ hχ
      have hmu := mul_mem_UAt hmv huv
      have c1 : Acts (evFin F v) (om (1, m * u)) φ χ₁ := by
        have := acts_mul v (hpres _) hact aχ₁
        rwa [← map_mul, Prod.mk_mul_mk, one_mul] at this
      have c2 : Acts (evFin F v) (om (1, m * u)) φ χ' := by
        have := acts_mul v (hpres _) aχ aχ'
        rwa [← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel_right] at this
      have e := uq 1 h1X (m * u) hmu φ hφ χ₁ χ' hχ₁ c1 hχ' c2
      refine ⟨sub_mem hφ₁ hφ, χ₁ - χ, sub_mem hχ₁ hχ, sub hφ₁ hφ aχ₁ aχ, ?_⟩
      refine GlobalTheory.JacquetLine.unipAug_le_jacKer om H' v
        (Submodule.subset_span ⟨_, conj_mem_unip hm hu, hu', χ, hχ, χ₁, hχ₁, ?_, rfl⟩)
      rw [e]; exact aχ'
  | zero =>
    obtain ⟨χ, hχ, aχ⟩ := exT 0 (SB _).zero_mem
    refine ⟨(SB _).zero_mem, 0, (SB _).zero_mem, ?_, Submodule.zero_mem _⟩
    simpa only [zero_smul] using smul 0 (SB _).zero_mem aχ
  | add x y _ _ hx hy =>
    obtain ⟨hxs, x₁, hx₁, ax, jx⟩ := hx
    obtain ⟨hys, y₁, hy₁, ay, jy⟩ := hy
    exact ⟨add_mem hxs hys, x₁ + y₁, add_mem hx₁ hy₁, add hxs hys ax ay, add_mem jx jy⟩
  | smul c x _ hx =>
    obtain ⟨hxs, x₁, hx₁, ax, jx⟩ := hx
    exact ⟨(SB _).smul_mem c hxs, c • x₁, (SB _).smul_mem c hx₁, smul c hxs ax, Submodule.smul_mem _ c jx⟩

end Core

end GlobalTheory.JacquetLevi

namespace GlobalTheory.JacquetLevi

theorem transport : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → m ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ' ∈ SB (Fin a × Fin (a + a') → Fv F v), φ - ψ - ψ' ∈ GlobalTheory.JacquetLine.jacKer om H' v → ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φ φ₁ → ∃ ψ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ ψ₁' ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) ψ ψ₁ ∧ Acts (evFin F v) (om (1, m)) ψ' ψ₁' ∧ φ₁ - ψ₁ - ψ₁' ∈ GlobalTheory.JacquetLine.jacKer om H' v := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ _ v _ t m hm hmv φ hφ ψ hψ ψ' hψ' hker φ₁ hφ₁ hact
  have P := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hEx := (GlobalTheory.T.theta_action_exists hKP.base F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ P v).1
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun x Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting P.weil).pres x Φ hΦ
  have h1X := one_mem_UAt (σ := σ) (X := G.V) v
  have exT : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φ φ₁ := fun φ hφ =>
    let ⟨φ₁, h1, _⟩ := hEx 1 h1X m hmv φ hφ
    ⟨φ₁, h1.1, h1.2⟩
  obtain ⟨ψ₁, hψ₁, aψ⟩ := exT ψ hψ
  obtain ⟨ψ₁', hψ₁', aψ'⟩ := exT ψ' hψ'
  have sub : ∀ {φ ψ φ₁ ψ₁}, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → ψ ∈ SB (Fin a × Fin (a + a') → Fv F v) →
      Acts (evFin F v) (om (1, m)) φ φ₁ → Acts (evFin F v) (om (1, m)) ψ ψ₁ →
      Acts (evFin F v) (om (1, m)) (φ - ψ) (φ₁ - ψ₁) := fun hφ hψ a b => by
    simpa only [one_smul, neg_one_smul, ← sub_eq_add_neg] using acts_lin v _ exT hφ hψ a b 1 (-1)
  have hs1 : φ - ψ ∈ SB (Fin a × Fin (a + a') → Fv F v) := sub_mem hφ hψ
  have hs2 : φ - ψ - ψ' ∈ SB (Fin a × Fin (a + a') → Fv F v) := sub_mem hs1 hψ'
  have a2 : Acts (evFin F v) (om (1, m)) (φ - ψ - ψ') (φ₁ - ψ₁ - ψ₁') := sub hs1 hψ' (sub hφ hψ hact aψ) aψ'
  obtain ⟨z₁, hz₁, az, jz⟩ := image_jacKer om H' v hEx hpres hm hmv hker
  have e : z₁ = φ₁ - ψ₁ - ψ₁' :=
    (hEx 1 h1X m hmv _ hs2).unique ⟨hz₁, az⟩ ⟨sub_mem (sub_mem hφ₁ hψ₁) hψ₁', a2⟩
  exact ⟨ψ₁, hψ₁, ψ₁', hψ₁', aψ, aψ', e ▸ jz⟩

end GlobalTheory.JacquetLevi
