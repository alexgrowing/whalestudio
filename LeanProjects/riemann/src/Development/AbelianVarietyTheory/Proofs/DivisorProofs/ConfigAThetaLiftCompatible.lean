import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.TwPartStab
open GlobalTheory.RealLift GlobalTheory.KInfPol
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem acts_zero {n d : ℕ} (T : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) :
    Acts (evI F) T ⇑(0 : SInf F (Fin n × Fin d)) ⇑(0 : SInf F (Fin n × Fin d)) := by
  intro r _
  have h0 : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r = 0 := by funext x; simp [tens]
  rw [h0, map_zero]

theorem acts_comp {κ : Type} [Fintype κ] {A B : Module.End ℂ ((κ → AF F) → ℂ)}
    (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ) {f f₁ f₂ : SInf F κ}
    (h₁ : Acts (evI F) A (⇑f) (⇑f₁)) (h₂ : Acts (evI F) B (⇑f₁) (⇑f₂)) :
    Acts (evI F) (B * A) (⇑f) (⇑f₂) := by
  intro r hr
  have e₁ := h₁ r hr
  have hr₁ : Rest (evI F) (⇑f₁) r := ⟨hr.1, by rw [← e₁]; exact hA _ hr.2⟩
  rw [Module.End.mul_apply, e₁]
  exact h₂ r hr₁

theorem acts_mul {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ}
    {χ₁ χ₂ : Chr F E} {om : Rep σ Y W} (hw : M.IsWeil ψ χ₁ χ₂ om) (h h' : UA σ W.J)
    {f f₁ f₂ : SInf F (Fin n × Fin d)} (h₁ : Acts (evI F) (om (1, h)) f f₁)
    (h₂ : Acts (evI F) (om (1, h')) f₁ f₂) : Acts (evI F) (om (1, h' * h)) f f₂ := by
  have hS := IsUWeilPair.isUSplitting hw
  have hc := acts_comp (fun Φ hΦ => hS.pres (1, h) Φ hΦ) h₁ h₂
  rwa [← map_mul, Prod.mk_mul_mk, one_mul] at hc

theorem descent {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {B : Base F E}
    {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (onto : (M.Pol B.ψ B.emb).map p = ⊤) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hker : ∀ f ∈ M.Pol B.ψ B.emb, p f = 0 → p (A f) = 0) :
    ∃ T : P →ₗ[ℂ] P, ∀ g ∈ M.Pol B.ψ B.emb, p (A g) = T (p g) := by
  let q : M.Pol B.ψ B.emb →ₗ[ℂ] P := p.domRestrict _
  let r : M.Pol B.ψ B.emb →ₗ[ℂ] P := (p ∘ₗ A).domRestrict _
  have hq : Function.Surjective q := by
    intro x
    have hx : x ∈ (M.Pol B.ψ B.emb).map p := onto ▸ Submodule.mem_top
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨⟨g, hg⟩, rfl⟩
  have hle : LinearMap.ker q ≤ LinearMap.ker r := fun g hg => hker g.1 g.2 hg
  refine ⟨(LinearMap.ker q).liftQ r hle ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap, fun g hg => ?_⟩
  have e : (q.quotKerEquivOfSurjective hq).symm (p g) = Submodule.Quotient.mk ⟨g, hg⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
  rfl

theorem fockDeg_stable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {B : Base F E}
    {χ₁ χ₂ : Chr F E} {om : Rep σ Y W} (hB : B.IsGood σ) (hw : M.IsWeil B.ψ χ₁ χ₂ om) {k : UA σ W.J}
    (hk : k ∈ KInf σ W B.emb) {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hA : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f (A f)) (j : ℕ) :
    fockDeg M B.ψ B.emb j ≤ (fockDeg M B.ψ B.emb j).comap A := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  induction j with
  | zero =>
    refine Submodule.span_le.2 fun f₀ hf₀ => Submodule.subset_span ?_
    obtain ⟨ε, hε⟩ := hf₀
    refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
    have hv := at_mul_right hu (mat k⁻¹)ᵀ
    have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
    have h1 := hint _ hv f₀
    have h2 := hint _ hv' f₀
    rw [hcan] at h1 h2
    have e1 := (hL _ _ _).2.2.1 _ hg h1
    have e2 := (hL _ _ _).2.2.1 _ hg' h2
    have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
    · rw [e1, e2, key, map_smul]
    · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
        rw [← Matrix.map_mul]
        change (mat (k⁻¹ * k)).map _ = 1
        rw [inv_mul_cancel]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
      have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
        calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
              ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
          _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
              (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
      rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
  | succ j ih =>
    rw [fockDeg_succ]
    refine sup_le (ih.trans (Submodule.comap_mono le_sup_left)) (Submodule.span_le.2 ?_)
    rintro φ₁ ⟨u, hu, φ, hφ, hφ₁⟩
    have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
    rw [e]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨_, at_mul_right hu _, A φ, ih hφ, hint u hu φ⟩)

theorem levi_comm {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {B : Base F E} {i₀ i₁ : ℕ}
    (hlat : W.L.IsLattice E) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {t : (AE F E)ˣ} {k₁ : UA σ W₁.J} {k z : UA σ W.J}
    (hk : IsLevi H' 1 k₁ k) (hz : IsLevi (W₁ := W₁) H' t 1 z) : k * z = z * k := by
  obtain ⟨hkx, hky, hkι⟩ := hk
  obtain ⟨hzx, hzy, hzι⟩ := hz
  simp only [Units.val_one, one_smul, inv_one, map_one] at hkx hky
  have h1 : mat (1 : UA σ W₁.J) = 1 := rfl
  set P := mat k * mat z - mat z * mat k with hP
  have hPx : P *ᵥ incV F H'.x = 0 := by
    rw [hP, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzx, Matrix.mulVec_smul, hkx, hzx, sub_self]
  have hPy : P *ᵥ incV F H'.y = 0 := by
    rw [hP, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzy, Matrix.mulVec_smul, hky, hzy, sub_self]
  have e1 : mat k * mat z * incM F H'.ι = incM F H'.ι * mat k₁ := by
    rw [Matrix.mul_assoc, hzι, h1, Matrix.mul_one, hkι]
  have e2 : mat z * mat k * incM F H'.ι = incM F H'.ι * mat k₁ := by
    rw [Matrix.mul_assoc, hkι, ← Matrix.mul_assoc, hzι, h1, Matrix.mul_one]
  have hPι : P * incM F H'.ι = 0 := by rw [hP, Matrix.sub_mul, e1, e2, sub_self]
  have iadd : ∀ v w : Fin d → E, incV F (v + w) = incV F v + incV F w := by
    intro v w; funext i; simp [incV, map_add]
  have ismul : ∀ (c : E) (v : Fin d → E), incV F (c • v) = inclR (F := F) (AF F) c • incV F v := by
    intro c v; funext i; simp [incV, map_mul]
  have imul : ∀ u : Fin d₁ → E, incV F (H'.ι *ᵥ u) = incM F H'.ι *ᵥ incV F u := by
    intro u; funext i; exact RingHom.map_mulVec _ _ _ i
  have hall : ∀ v : Fin d → E, P *ᵥ incV F v = 0 := by
    intro v
    have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by rw [hlat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨s, t', u, -, -, -, rfl⟩ := hH.split v hv
      rw [iadd, iadd, ismul, ismul, imul, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hPx, hPy, Matrix.mulVec_mulVec, hPι, Matrix.zero_mulVec]
      simp
    | zero =>
      have : incV F (0 : Fin d → E) = 0 := by funext i; simp [incV]
      rw [this, Matrix.mulVec_zero]
    | add v w _ _ hv hw => rw [iadd, Matrix.mulVec_add, hv, hw, add_zero]
    | smul c v _ hv => rw [ismul, Matrix.mulVec_smul, hv, smul_zero]
  have hP0 : P = 0 := by
    ext i j
    have hj := congrFun (hall (Pi.single j 1)) i
    have hs : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext l; by_cases h : l = j
      · subst h; simp [incV]
      · simp [incV, Pi.single_apply, h]
    rw [hs, Matrix.mulVec_single_one] at hj
    simpa using hj
  apply Subtype.ext
  apply Units.ext
  exact sub_eq_zero.1 hP0

theorem kStabL_twPart : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      KStabL B G.M om R.p G₁.W H' (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm _
  have hB := hm.triple.base
  have hM := hm.triple.geo.hM
  have hw := hm.triple.weil
  have hlat := hm.triple.geo.hW.lat
  have hL := actsLaws F (Fin (b + 2) × Fin (b + 2 + a'))
  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      (∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (1, k)) f (A f)) ∧
      ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ g ∈ G.M.Pol B.ψ B.emb, R.p (A g) = T (R.p g) := by
    intro k hk
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk
    refine ⟨A, hA, descent R.p hm.real.quot.onto A fun f hf hpf => ?_⟩
    have h0 := hm.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (acts_zero _) (by rw [hpf, map_zero])
    rw [h0, map_zero]
  intro k hk k₁ hk₁ hLk f hf f₁ hAct hpf
  obtain ⟨A, hA, T, hT⟩ := hop k hk
  have e₁ : f₁ = A f := (hL f f₁ (A f)).2.2.2.1 _ hAct (hA f)
  rw [e₁, hT f hf]
  revert hpf
  suffices h : twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ≤
      (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).comap T from fun hpf => h hpf
  refine Submodule.span_le.2 ?_
  rintro x ⟨hxV, hxE⟩
  obtain ⟨g, hg, rfl⟩ := hxV
  have hgP : g ∈ G.M.Pol B.ψ B.emb := fockDeg_le_pol _ _ _ _ hg
  refine Submodule.subset_span ⟨⟨A g, fockDeg_stable hB hw hk hA _ hg, hT g hgP⟩, ?_⟩
  intro k' hk' t hLt f' hf' f₁' hAct' hpf'
  obtain ⟨A', hA', T', hT'⟩ := hop k' hk'
  have e' : f₁' = A' f' := (hL _ _ _).2.2.2.1 _ hAct' (hA' f')
  rw [e', hT' f' hf', hpf', ← hT g hgP]
  have hAgP : A g ∈ G.M.Pol B.ψ B.emb := GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk g hgP (A g) (hA g)
  have hA'gP : A' g ∈ G.M.Pol B.ψ B.emb :=
    GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k' hk' g hgP (A' g) (hA' g)
  rw [← hT' _ hAgP]
  have hcomm : k * k' = k' * k := levi_comm hlat hcfg.hH' hLk hLt
  have c1 := acts_mul hw k k' (hA g) (hA' (A g))
  have c2 := acts_mul hw k' k (hA' g) (hA (A' g))
  rw [hcomm] at c2
  have e2 : A' (A g) = A (A' g) := (hL _ _ _).2.2.2.1 _ c1 c2
  rw [e2, hT _ hA'gP, hxE k' hk' t hLt g hgP (A' g) (hA' g) rfl, map_smul, hT g hgP]

end GlobalTheory.TwPartStab
