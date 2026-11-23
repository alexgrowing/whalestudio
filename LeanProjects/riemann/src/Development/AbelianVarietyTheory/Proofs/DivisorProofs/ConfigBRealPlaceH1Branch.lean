import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaLiftCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaLiftVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaLiftRecursionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCompactLeviLiftStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem one_mem_KInf_of_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {m : ℕ} (X : Spc F E m) (τ : ∀ w : InfinitePlace F, EmbOver E w) : (1 : UA σ X.J) ∈ KInf σ X τ := by
  refine ⟨fun u _ => ?_, fun w => ?_⟩
  · have : mat (1 : UA σ X.J) - 1 = 0 := by simp [mat]
    rw [this, smul_zero]
  · have : (mat (1 : UA σ X.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _

theorem frobInf_offEig_of_beta {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H' : Plane E (a + (b + 2)) (a + b)}
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a (b + 2)} {Rf : FinMaps F a (b + 2)}
    {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W} {R₁ : RealMaps F a b} {Rf₁ : FinMaps F a b}
    (hM : IsMatched B G X om om' R Rf) (hM₁ : IsMatched B G₁ X om₁ om₁' R₁ Rf₁) {φ : R.Pi →ₗ[ℂ] R₁.Pi}
    (hφ : IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ) {x : R.Pi}
    (hx : IsOffEig B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) x) : φ x = 0 := by
  obtain ⟨k, hk, t, hL, c, hc, hx⟩ := hx
  have hx0 : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx0
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hM.triple.base hM.triple.geo.hM
    hM.triple.weil k hk
  have h1 := hx f hf (A f) (hA f) rfl
  have hy0 : φ (R.p f) ∈ (G₁.M.Pol B.ψ B.emb).map R₁.p := by rw [hM₁.real.quot.onto]; exact Submodule.mem_top
  obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.1 hy0
  have hacts : Acts (evI F) (om₁ (1, 1)) g g := by
    intro r _
    rw [show ((1 : UA σ G₁.V.J), (1 : UA σ G₁.W.J)) = 1 from rfl, map_one]
    rfl
  have h2 := hφ.cpt k hk t 1 hL (one_mem_KInf_of_real G₁.W B.emb) f hf (A f) (hA f) g hg g hacts hgx.symm
  rw [h1, map_smul, hgx] at h2
  have h3 : (c - (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • φ (R.p f) = 0 := by
    rw [sub_smul, h2, sub_self]
  exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)

theorem config_b_real_place_branch : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ π : R.Pi →ₗ[ℂ] R₁.Pi, (∀ x ∈ lowPartInf B G.M R.p, π x ∈ lowPartInf B G₁.M R₁.p) ∧
        ∀ φ : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ →
          ∃ T : R₁.Pi →ₗ[ℂ] R₁.Pi, KEqOn B G₁.M om₁ R₁.p (lowPartInf B G₁.M R₁.p) T ∧
            ∀ x ∈ lowPartInf B G.M R.p, φ x = T (π x) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hdec := GlobalTheory.T.config_b_theta_lift_compatible hK F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hdis := GlobalTheory.T.config_b_theta_lift_vanishing hK F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨ι, hinj, himg, hstab, heq⟩ := GlobalTheory.T.config_b_theta_lift_recursion hK F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hlevi := GlobalTheory.T.infinite_compact_levi_lift F E σ B a b G G₁ H H' hC hM.triple.base hM.triple.geo hM₁.triple.geo
  set V := lowPartInf B G.M R.p with hV
  set tw := twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) V with htw
  set off := offPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) V with hoffd
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl (tw ⊔ off)
  have hcompl : IsCompl tw (off ⊔ C₀) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨o, ho, c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
      have hc' : c ∈ tw ⊔ off := by
        have e : c = (o + c) - o := by abel
        rw [e]; exact Submodule.sub_mem _ (Submodule.mem_sup_left hx) (Submodule.mem_sup_right ho)
      have hc0 : c = 0 := (Submodule.disjoint_def.1 hC₀.disjoint) c hc' hc
      subst hc0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 hdis) o hx ho
    · rw [codisjoint_iff, ← sup_assoc]; exact hC₀.sup_eq_top
  set pr := Submodule.linearProjOfIsCompl tw (off ⊔ C₀) hcompl with hpr
  have hpr_tw : ∀ y ∈ tw, ((pr y : tw) : R.Pi) = y := fun y hy => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hcompl ⟨y, hy⟩)
  have hpr_off : ∀ o ∈ off, pr o = 0 := fun o ho =>
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hcompl).2 (Submodule.mem_sup_left ho)
  have hπ : ∀ y ∈ tw, ∀ o ∈ off, ι ((pr (y + o) : tw) : R.Pi) = ι y := fun y hy o ho => by
    rw [map_add, hpr_off o ho, add_zero, hpr_tw y hy]
  have hker : LinearMap.ker (ι ∘ₗ tw.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    exact Subtype.ext (hinj y y.2 hy)
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (ι ∘ₗ tw.subtype) hker
  have hsι : ∀ y ∈ tw, ((s (ι y) : tw) : R.Pi) = y := fun y hy => by
    have e := LinearMap.congr_fun hs ⟨y, hy⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at e
    rw [e]
  refine ⟨ι ∘ₗ tw.subtype ∘ₗ pr, ?_, fun φ hφ => ?_⟩
  · intro x hx
    obtain ⟨y, hy, o, ho, rfl⟩ := Submodule.mem_sup.1 (hdec hx)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hπ y hy o ho, ← himg]
    exact Submodule.mem_map_of_mem hy
  · have hoff : ∀ z ∈ off, φ z = 0 := fun z hz => LinearMap.mem_ker.1 ((Submodule.span_le.2 fun y hy =>
      LinearMap.mem_ker.2 (frobInf_offEig_of_beta hM hM₁ hφ hy.2)) hz)
    refine ⟨φ ∘ₗ tw.subtype ∘ₗ s, ?_, ?_⟩
    · intro k₁ hk₁ f hf f₁ hf₁ hfV g hg g₁ hg₁ hT
      rw [← himg] at hfV
      obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.1 hfV
      obtain ⟨k, hk, hL⟩ := hlevi k₁ hk₁
      have hy0 : y ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; exact Submodule.mem_top
      obtain ⟨f', hf', rfl⟩ := Submodule.mem_map.1 hy0
      obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hM.triple.base hM.triple.geo.hM
        hM.triple.weil k hk
      have h1 : ι (R.p (A f')) = R₁.p f₁ := heq k hk k₁ hk₁ hL f' hf' (A f') (hA f') hy f hf f₁ hf₁ hyf
      have h2 : R.p (A f') ∈ tw := hstab k hk k₁ hk₁ hL f' hf' (A f') (hA f') hy
      have hT' : φ (R.p f') = R₁.p g := by
        have e := hT
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
        rw [← hyf, hsι _ hy] at e
        exact e
      have h3 := hφ.cpt k hk 1 k₁ hL hk₁ f' hf' (A f') (hA f') g hg g₁ hg₁ hT'
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← h1, hsι _ h2, h3]
      simp
    · intro x hx
      obtain ⟨y, hy, o, ho, rfl⟩ := Submodule.mem_sup.1 (hdec hx)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hπ y hy o ho, hsι y hy, map_add, hoff o ho, add_zero]

end GlobalTheory.IndLine
