import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPairSelfDualLatticeIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEtaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThKEvKernel

open GlobalTheory.KTowerPlane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem form_sub_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a - b) = form σ J c a - form σ J c b := by
  rw [sub_eq_add_neg, form_add_right, ← neg_one_smul E b, form_smul_right]; simp [sub_eq_add_neg]

theorem exists_lattice {B : Base F E} (hB : B.IsGood σ) {n : ℕ} {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s)
    (x y : Fin n → E) (hxx : form σ Y.J x x = 0) (hyy : form σ Y.J y y = 0) (hxy : form σ Y.J x y = 1) :
    ∃ L : Submodule (𝓞 E) (Fin n → E), L.IsLattice E ∧ (∀ z, z ∈ L ↔ ∀ t ∈ L, IsIntegral ℤ (form σ Y.J z t)) ∧
      ∀ z ∈ L, form σ Y.J z y • x ∈ L ∧ form σ Y.J z x • y ∈ L := by
  classical
  have hcm : IsCMExt F E σ := hB.cm
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hcm
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by haveI := hB.unram; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module F E σ n Y.J Y.L hY.lat.fg x
    (GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hY.lat.fg hY.herm hY.dual x hx0)
  obtain ⟨y', hyy', hxy', hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x y₀ hxx hy₀1 hy₀L
  have sw : ∀ a b, form σ Y.J b a = σ (form σ Y.J a b) := form_swap hcm hY.herm
  have hyx : form σ Y.J y x = 1 := by rw [sw, hxy, map_one]
  obtain ⟨w, hw⟩ : ∃ w, w = y' - y := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = -form σ Y.J y y' := ⟨_, rfl⟩
  have hxw : form σ Y.J x w = 0 := by rw [hw, form_sub_right, hxy, hxy', sub_self]
  have hwx : form σ Y.J w x = 0 := by rw [sw, hxw, map_zero]
  have hyw : form σ Y.J y w = -μ := by rw [hw, form_sub_right, hyy, hμ]; ring
  have hww : form σ Y.J w w = μ + σ μ := by
    rw [hμ, map_neg, ← sw, hw, form_sub_left, form_sub_right, form_sub_right, hyy, hyy']; ring
  let g : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun z => z + form σ Y.J z x • w - (form σ Y.J z w + μ * form σ Y.J z x) • x
      map_add' := fun a b => by simp only [form_add_left]; module
      map_smul' := fun c a => by simp only [form_smul_left, RingHom.id_apply]; module }
  have hg : ∀ z, g z = z + form σ Y.J z x • w - (form σ Y.J z w + μ * form σ Y.J z x) • x := fun z => rfl
  have hgx : g x = x := by rw [hg, hxx, hxw]; simp
  have hgy : g y = y' := by rw [hg, hyx, hyw, hw]; simp
  have hiso : ∀ a b, form σ Y.J (g a) (g b) = form σ Y.J a b := fun a b => by
    rw [hg, hg]
    simp only [form_sub_left, form_add_left, form_smul_left, form_sub_right, form_add_right, form_smul_right, hxx, hxw,
      hwx, hww, map_add, map_mul]
    rw [sw b w, sw b x]
    ring
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra h0
    obtain ⟨t, -, ht⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hY.lat.fg hY.herm hY.dual z h0
    apply ht
    rw [← hiso, hz]; simp [form, ← Pi.zero_def]
  have hsurj : Function.Surjective g := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective g (LinearMap.ker_eq_bot.2 hinj)
  have hP : LinearMap.toMatrix' g' * LinearMap.toMatrix' g = 1 := by
    rw [← LinearMap.toMatrix'_comp, hg', LinearMap.toMatrix'_id]
  have hmem : ∀ z, z ∈ Y.L.comap ((Matrix.mulVecLin (LinearMap.toMatrix' g)).restrictScalars (𝓞 E)) ↔ g z ∈ Y.L :=
    fun z => by
      show LinearMap.toMatrix' g *ᵥ z ∈ Y.L ↔ _
      rw [LinearMap.toMatrix'_mulVec]
  refine ⟨_, GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix E n n Y.L _ _ hP hY.lat, fun z => ?_, fun z hz => ?_⟩
  · rw [hmem, hY.dual]
    refine ⟨fun H t ht => ?_, fun H t ht => ?_⟩
    · rw [← hiso]; exact H _ ((hmem t).1 ht)
    · obtain ⟨t, rfl⟩ := hsurj t
      rw [hiso]; exact H t ((hmem t).2 ht)
  · rw [hmem] at hz
    rw [hmem, hmem, map_smul, map_smul, hgx, hgy, ← hiso z y, ← hiso z x, hgx, hgy]
    exact hL _ hz

theorem compl_onto {n n₁ : ℕ} (hn : n = n₁ + 2) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (ι : Matrix (Fin n) (Fin n₁) E) (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hι : Function.Injective ι.mulVec) (z : Fin n → E) (h1 : form σ J z x = 0) (h2 : form σ J z y = 0) :
    ∃ u, z = ι *ᵥ u := by
  obtain ⟨ι₀, P₀, hP₀, -, hcomp⟩ := GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair F E σ n n₁ J x y hn hJ hxx hyy hxy
  have key : ∀ u, ι₀ *ᵥ ((P₀ * ι) *ᵥ u) = ι *ᵥ u := fun u => by
    obtain ⟨u', hu'⟩ := hcomp _ (horth u).1 (horth u).2
    rw [← Matrix.mulVec_mulVec, hu', Matrix.mulVec_mulVec u' P₀, hP₀, Matrix.one_mulVec]
  have hinj : Function.Injective (Matrix.mulVecLin (P₀ * ι)) := fun a b hab => hι (by
    have hab' : (P₀ * ι) *ᵥ a = (P₀ * ι) *ᵥ b := hab
    rw [← key, ← key, hab'])
  obtain ⟨u₀, rfl⟩ := hcomp z h1 h2
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj u₀
  exact ⟨u, by rw [← key, ← hu]; rfl⟩

theorem exists_adapted {B : Base F E} (hB : B.IsGood σ) (hE : ∀ v, v ∉ B.P) {n n₁ : ℕ} (hn : n = n₁ + 2)
    {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s) (x y : Fin n → E) (hxx : form σ Y.J x x = 0)
    (hyy : form σ Y.J y y = 0) (hxy : form σ Y.J x y = 1) (ι : Matrix (Fin n) (Fin n₁) E)
    (horth : ∀ u, form σ Y.J (ι *ᵥ u) x = 0 ∧ form σ Y.J (ι *ᵥ u) y = 0) (hι : Function.Injective ι.mulVec)
    (Y₁ : Spc F E n₁) (hJ₁ : Y₁.J = ιᵀ * Y.J * ι.map σ) :
    ∃ L θ L₁ θ₁ 𝔟, (⟨Y.J, L, θ, Y.bas⟩ : Spc F E n).IsHerm σ B r s ∧
      (⟨Y₁.J, L₁, θ₁, Y₁.bas⟩ : Spc F E n₁).IsHerm σ B (r - 1) (s - 1) ∧
      (⟨x, y, ι, 𝔟⟩ : Plane E n n₁).IsAdapted σ B ⟨Y.J, L, θ, Y.bas⟩ ⟨Y₁.J, L₁, θ₁, Y₁.bas⟩ 0 1 := by
  classical
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨L, hlat, hdual, hL⟩ := exists_lattice hB hY x y hxx hyy hxy
  have hcomp := compl_onto hn hY.herm x y hxx hyy hxy ι horth hι
  obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin ι) (LinearMap.ker_eq_bot.2 hι)
  obtain ⟨P, hPι⟩ : ∃ P : Matrix (Fin n₁) (Fin n) E, P * ι = 1 := by
    refine ⟨LinearMap.toMatrix' g', ?_⟩
    have := congrArg LinearMap.toMatrix' hg'
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  have hyx : form σ Y.J y x = 1 := by rw [form_swap hcm hY.herm, hxy, map_one]
  have hsplit : ∀ z ∈ L, ∃ u, ι *ᵥ u ∈ L ∧ z = form σ Y.J z y • x + ι *ᵥ u + form σ Y.J z x • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - form σ Y.J z x • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]; ring) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    refine ⟨u, ?_, ?_⟩
    · rw [← hu]; exact L.sub_mem (L.sub_mem hz (hL z hz).1) (hL z hz).2
    · rw [← hu]; abel
  set L₁ := L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsLattice E := GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix E n n₁ L ι P hPι hlat
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients E n L hlat x hx0
  have hform₁ : ∀ u u', form σ Y₁.J u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := by rw [hJ₁]; exact form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hMh : ∀ w, (Y.J.map (e w))ᴴ = Y.J.map (e w) := fun w => map_herm hcm _ hY.herm
  have cxx : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (x i)) = 0 := fun w => by
    rw [← map_form hcm, hxx, map_zero]
  have cyy : ∀ w, (fun i => e w (y i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 0 := fun w => by
    rw [← map_form hcm, hyy, map_zero]
  have cxy : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 1 := fun w => by
    rw [← map_form hcm, hxy, map_one]
  have cox : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (x i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι x (fun u => (horth u).1)
  have coy : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (y i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι y (fun u => (horth u).2)
  have cP : ∀ w, P.map (e w) * ι.map (e w) = 1 := fun w => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have cg : ∀ w, (ι.map (e w))ᵀ * Y.J.map (e w) * (ι.map (e w)).map star = Y₁.J.map (e w) := fun w => by
    rw [hJ₁]; exact map_gram hcm _ Y.J ι
  have hsig₁ : ∀ w, HasSig (Y₁.J.map (e w)) (r - 1) (s - 1) := fun w => by
    rw [← cg w]
    exact GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane n n₁ _ _ _ _ _ r s hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (hY.sig w)
  have hθ₁ : ∀ w, ∃ θ, IsCartan (Y₁.J.map (e w)) θ := fun w => GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature n₁ _ _ _ (hsig₁ w)
  choose θ₁ hθ₁ using hθ₁
  have hθ : ∀ w, ∃ θ, IsCartan (Y.J.map (e w)) θ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ w ∧
      θ *ᵥ (fun i => e w (x i)) = fun i => e w (y i) := fun w =>
    GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair n n₁ _ _ _ _ _ _ hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (by rw [cg w]; exact hθ₁ w)
  choose θ hθ using hθ
  refine ⟨L, θ, L₁, θ₁, 𝔟, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hlat, dual := hdual, cartan := fun w => (hθ w).1
            bas := fun v => (hE _ v.2).elim }
  · exact { herm := fun i j => by
              show σ (Y₁.J j i) = Y₁.J i j
              rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform₁, hform₁,
                form_swap hcm hY.herm (ι *ᵥ Pi.single j 1) (ι *ᵥ Pi.single i 1)]
            sig := hsig₁
            lat := hlat₁
            dual := fun u => by
              show u ∈ L₁ ↔ ∀ u' ∈ L₁, IsIntegral ℤ (form σ Y₁.J u u')
              refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
              · rw [hform₁]; exact (hdual _).1 hu _ hu'
              · show ι *ᵥ u ∈ L
                refine (hdual _).2 fun z hz => ?_
                obtain ⟨u', hu', hz'⟩ := hsplit z hz
                rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
                  (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
                exact H u' hu'
            cartan := hθ₁
            bas := fun v => (hE _ v.2).elim }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := hJ₁.symm, low := fun u => Iff.rfl
            split := fun z hz => by
              obtain ⟨u, hu, hz'⟩ := hsplit z hz
              exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩
            ideal := h𝔟
            cartan := fun w => ⟨(hθ w).2.1, 1, one_ne_zero, by rw [one_smul]; exact (hθ w).2.2.symm⟩
            bas := fun v => (hE _ v.2).elim }

theorem exists_vac {B : Base F E} (hB : B.IsGood σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ}
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (hco : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (hμ : M.μ.IsHaarMeasure) (hdom : IsFundamentalDomain (ratU σ X.J) M.dom M.μ) :
    ∃ vac, (⟨M.co, vac, M.μ, M.dom⟩ : Model σ X W).IsGood B.ψ := by
  classical
  have hS := GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW M.co hco
  let M₀ : Model σ X W := ⟨M.co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X W r s r' s' hX hW M.co v).choose
  refine ⟨vac, ⟨hco, fun v => ?_, ?_, hμ, hdom⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X W r s r' s' hX hW M.co v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv

theorem admissible_comp_eval {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {ι ι' I e}
    (hE : IsEv B M M₁ ι ι' I e) :
    ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro l hl g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hfam : ∀ j, ∀ᶠ v in Filter.cofinite, φ j v = M.vac v := fun j =>
    ((hstd j).and hM.std).mono fun v hv => hv.1.trans hv.2.symm
  have hψSB : ∀ j v, ev v (φ j v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun j v =>
    (hev v).2 ▸ Submodule.mem_map_of_mem (hφ j v)
  have hψstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      ev v (φ j v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hfam j).and hM₁.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]
  have hG : ∀ j, (fun y : Fin n₁ × Fin d₁ → Af F => ∏ᶠ v, ev v (φ j v) fun i => evalV F v (y i)) ∈
      SB (Fin n₁ × Fin d₁ → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  choose Tj hTj using fun j => hl _ (hG j)
  refine ⟨∑ j, c j • (Tj j).comp ei, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  rw [LinearMap.comp_apply, hsplit, map_sum, map_sum]
  simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hloc f (φ j) (hφ j) (hfam j)]
  exact congrArg (c j • ·) (hTj j (ei f))

theorem thetaSum_smul {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem kernel_basic : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (n₁ : ℕ) (H : Plane E n n₁), (n₁ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
          (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (X₁ : Spc F E n₁) (M₁ : Model σ X₁ W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d), X₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ →
      IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Continuous (fun h : UA σ W.J => thetaSum F (e (om (1, h) Ψ))) ∧
        (∀ γ ∈ ratU σ W.J, ∀ h, thetaSum F (e (om (1, γ * h) Ψ)) = thetaSum F (e (om (1, h) Ψ))) ∧
        ∃ (C : ℝ) (k : ℕ), ∀ h, ‖thetaSum F (e (om (1, h) Ψ))‖ ≤ C * (ht h : ℝ) ^ k := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ H hH X₁ M₁ e hJ hM₁ he Ψ hΨ
  obtain ⟨hn, hxx, hyy, hxy, horth, hι⟩ := hH
  let B' : Base F E := ⟨B.ψ, B.emb, B.mα, B.mβ, ∅, fun v => (Finset.notMem_empty _ v.2).elim, B.v₁, B.τ₁⟩
  have hE : ∀ v, v ∉ B'.P := fun v => Finset.notMem_empty v
  have hB' : B'.IsGood σ := ⟨hP.base.cm, hP.base.galois, hP.base.unram, hP.base.std, hP.base.inert,
    fun v hv => (hE v hv).elim⟩
  have hX : X.IsHerm σ B' r s := ⟨hP.herm.herm, hP.herm.sig, hP.herm.lat, hP.herm.dual, hP.herm.cartan,
    fun v => (hE _ v.2).elim⟩
  have hW : W.IsSkew σ B' r' s' := ⟨hP.skew.skew, hP.skew.sig, hP.skew.lat, hP.skew.dual, hP.skew.cartan,
    fun v => (hE _ v.2).elim⟩
  obtain ⟨L, θ, L₁, θ₁, 𝔟, hX', hX₁', hH'⟩ :=
    exists_adapted hB' hE hn.symm hX H.x H.y hxx hyy hxy H.ι horth hι X₁ hJ
  obtain ⟨vac, hM'⟩ := exists_vac hB' hX' hW ⟨M.co, M.vac, M.μ, M.dom⟩ hP.good.rat hP.good.haar hP.good.dom
  obtain ⟨vac₁, hM₁'⟩ := exists_vac hB' hX₁' hW ⟨M₁.co, M₁.vac, M₁.μ, M₁.dom⟩ hM₁.rat hM₁.haar hM₁.dom
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n₁ := fun a => by
    rw [hP.resX a, ← hn]; simp [pow_add]
  obtain ⟨om₁, hom₁⟩ := GlobalTheory.T.hecke_characters_restriction_eta hKP.base F E σ B' hB' n₁ d _ W _ _ _ _ hX₁' hW _ hM₁' χX χW hP.hX hP.hW hres hP.resW
  have hP' : IsPair B' (⟨M.co, vac, M.μ, M.dom⟩ : Model σ ⟨X.J, L, θ, X.bas⟩ W) χX χW
      (show Rep σ ⟨X.J, L, θ, X.bas⟩ W from om) r s r' s' :=
    ⟨hB', hX', hW, hM', hP.hX, hP.hW, hP.resX, hP.resW, hP.weil⟩
  have hP₁' := IsPair.mk hB' hX₁' hW hM₁' hP.hX hP.hW hres hP.resW hom₁
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.adapted_plane_pair_restriction hKP.base F E σ B' n d _ W _ χX χW _ _ _ _ _ hP' n₁ _ _ 0 1 _ om₁ _ _ hH' hP₁'
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_adapted_plane_seesaw hKP.base F E σ B' n d _ W _ χX χW _ _ _ _ _ hP' n₁ _ _ 0 1 _ om₁ _ _ hH' hP₁' e₀ he₀
    e he.maps he.Heisenberg₂ he.inv (admissible_comp_eval hP.good hM₁ he)
  have hcomm := GlobalTheory.T.adapted_plane_pair_local_factor hKP.base F E σ B' n d _ W _ χX χW _ _ _ _ _ hP' n₁ _ _ 0 1 _ om₁ _ _ hH' hP₁' e₀ he₀
  have hS := IsUWeilPair.isUSplitting hP.weil
  have key : ∀ h : UA σ W.J, thetaSum F (e (om (1, h) Ψ)) = c * theta om₁ (e₀ Ψ) 1 h := fun h => by
    rw [hc _ (hS.pres _ _ hΨ), thetaSum_smul]
    exact congrArg (fun t => c * thetaSum F t) (hcomm h Ψ hΨ)
  obtain ⟨hcont, hinv, C, k, hC⟩ :=
    (GlobalTheory.T.theta_basic_properties hKP.base F E σ B' n₁ d _ W _ χX χW om₁ _ _ _ _ hP₁').1 (e₀ Ψ) (he₀.maps Ψ hΨ)
  simp only [key]
  refine ⟨continuous_const.mul (hcont.comp (Continuous.prodMk_right 1)), fun γ hγ h => ?_,
    ‖c‖ * C * (ht (1 : UA σ X₁.J) : ℝ) ^ k, k, fun h => ?_⟩
  · have := hinv 1 (one_mem _) γ hγ 1 h
    rw [mul_one] at this
    rw [this]
  · rw [norm_mul, mul_assoc, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (hC 1 h) (norm_nonneg c)

end GlobalTheory.ThKEvKernel

end
