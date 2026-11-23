import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.AHWeilAny

theorem exists_cubical (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left)
    (hL : L.IsLB) : ∃ M : RigLB A, M.L = L ∧ Nonempty (CubicalStr A M) := by
  obtain ⟨r, hr⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local (V := ℂ) (L.pull (eSec A)) (pull_isLB hL _)
  let M : RigLB A := ⟨L, r, hL, hr⟩
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds ℂ A hA
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA) L hL
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hL t ht
  exact ⟨M, rfl, ⟨GlobalTheory.AbLaw.Cube.cubicalOfNormalised GlobalTheory.globalFns_holds hA M t' ht' hn⟩⟩

theorem exists_thetaGrp (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left)
    (hL : L.IsLB) (k : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (hx : x ^ k = 1) :
    ∃ θ : Out.ThetaGrp A L k (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)),
      θ.pt = Out.overResι ⊤ ≫ x := by
  obtain ⟨M, rfl, ⟨c⟩⟩ := exists_cubical A hA L hL
  haveI : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  let p₀ : (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)).left := ⟨(default : PrimeSpectrum ℂ), trivial⟩
  have hT : ∀ p : (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)).left, p = p₀ := fun p =>
    Subtype.ext (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _)
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.DescentPairing.exists_theta c p₀ hT k (Out.overResι ⊤ ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  exact ⟨θ, hθ⟩

theorem exists_chart_at {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    ∃ i, ⊤ ≤ x.left ⁻¹ᵁ L.U i := by
  have hv := GlobalTheory.valAt'_rules
  have : (show Sp ℂ ⟶ A.left from x.left) (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨i, ((hv _ x.left).1 _).2 hi⟩

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {n : ℕ} (u : HolUnif A L n)
    {Hm : Matrix (Fin n) (Fin n) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) :
    ∃ e : ℤ, (e : ℝ) = ((l : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin n → ℂ))).im := by
  obtain ⟨hH, -, hχ, hfr⟩ := h
  obtain ⟨i, hi⟩ := exists_chart_at hL (u.ex 0)
  have hl : ∀ z, ∀ w ∈ u.Λ, u.ex (z + w) = u.ex z := fun z w hw => by
    rw [u.ex_add, (u.ker w).2 hw, _root_.mul_one]
  have mem : ∀ w ∈ u.Λ, ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U i := fun w hw => by
    have e := hl 0 w hw
    rw [zero_add] at e
    rw [e]; exact hi
  have lm : (l : Fin n → ℂ) + m ∈ u.Λ := u.Λ.add_mem l.2 m.2
  have f1 := hfr l i 0 hi
  have f2 := hfr m i l (mem _ l.2)
  have f3 := hfr m i 0 hi
  have f4 := hfr l i m (mem _ m.2)
  have n0 := u.fr_ne i _ (mem _ lm)
  rw [zero_add] at f1 f3
  rw [add_comm (m : Fin n → ℂ) l] at f4
  rw [f2] at f1
  rw [f4] at f3
  have nl : χ l ≠ 0 := fun h0 => by simpa [h0] using hχ l
  have nm : χ m ≠ 0 := fun h0 => by simpa [h0] using hχ m
  simp only [zero_dotProduct, mul_zero, zero_add, Complex.exp_add] at f1 f3
  have key : cexp (Real.pi * ((l : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin n → ℂ)))) =
      cexp (Real.pi * ((m : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin n → ℂ)))) := by
    have nz : χ l * χ m * cexp (Real.pi / 2 * ((l : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin n → ℂ)))) *
        cexp (Real.pi / 2 * ((m : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin n → ℂ)))) *
        u.fr i ((l : Fin n → ℂ) + m) ≠ 0 := by
      have := Complex.exp_ne_zero
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨⟨nl, nm⟩, Complex.exp_ne_zero _⟩, Complex.exp_ne_zero _⟩, n0⟩
    apply mul_right_cancel₀ nz
    linear_combination f3 - f1
  have h1 : (m : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin n → ℂ)) =
      star ((l : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin n → ℂ))) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  rw [h1, Complex.exp_eq_exp_iff_exists_int] at key
  obtain ⟨N, hN⟩ := key
  refine ⟨N, ?_⟩
  generalize ((l : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin n → ℂ))) = w at hN ⊢
  have hi' := congrArg Complex.im hN
  simp [Complex.mul_im] at hi'
  have hp := Real.pi_pos
  have h2 : Real.pi * (2 * (w.im - N)) = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hp.ne'
  · linarith

theorem thetaGrp_in_frame {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {n : ℕ} (u : HolUnif A L n)
    {Hm : Matrix (Fin n) (Fin n) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) (k : ℕ) (a : u.Λ) (hk : 0 < k)
    (T : Over (Sp ℂ)) (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (θ : Out.ThetaGrp A L k T)
    (hθ : p ≫ θ.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin n → ℂ))) :
    ∃ C : ℂ, ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin n → ℂ))).left ⁻¹ᵁ L.U (j 1) →
      valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin n → ℂ)) ^ k =
        C * cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin n → ℂ))))) * u.fr (j 0) z ^ k := by
  have hv := GlobalTheory.valAt'_rules
  have hp := GlobalTheory.holFamily_lift hv
  have hint := im_hermForm_int hL u hAH
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨hH, -, hχ, hfr⟩ := hAH
  set b : Fin n → ℂ := (k : ℂ)⁻¹ • (a : Fin n → ℂ) with hb
  have h₀ : ∀ z, (lift p (u.ex z)).left ≫ (snd T A).left = (u.ex z).left := fun z => by
    rw [← Over.comp_left, lift_snd]
  have h₁ : ∀ z, (lift p (u.ex z)).left ≫ (Out.translPt A θ.pt).left = (u.ex (z + b)).left :=
    fun z => by rw [← Over.comp_left, ThetaGroupFrame.lift_translPt, hθ, ← u.ex_add, add_comm]
  have hl : ∀ z, ∀ l ∈ u.Λ, u.ex (z + l) = u.ex z := fun z l hl => by
    rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  have hl' : ∀ z, ∀ l ∈ u.Λ, u.ex (z + l + b) = u.ex (z + b) := fun z l h => by
    rw [add_right_comm, hl _ _ h]
  let V : L.ι → Set (Fin n → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}
  have hV : ∀ i, IsOpen (V i) := fun i => (u.hol _ 0).1
  have hVc : ∀ z, ∃ i, z ∈ V i := fun z => exists_chart_at hL (u.ex z)
  let D : (Fin 2 → L.ι) → Set (Fin n → ℂ) := fun j => V (j 0) ∩ (fun z => z + b) ⁻¹' V (j 1)
  let F : (Fin 2 → L.ι) → (Fin n → ℂ) → ℂ := fun j z =>
    valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val
  have hF : ∀ j, DifferentiableOn ℂ (F j) (D j) := fun j => by
    have h := (hp (Fin n → ℂ) Set.univ T A (fun _ => p) u.ex
      (fun U f => ⟨by simpa using isOpen_const, differentiableOn_const _⟩)
      (fun U f => by simpa using u.hol U f) _ (θ.φ.s j).val).2
    refine h.mono fun z hz => ⟨trivial, ?_⟩
    exact (ThetaGroupFrame.top_le_wchart_two L _ _ j _ _ _ (h₀ z) (h₁ z)).2 hz
  let G : (Fin 2 → L.ι) → (Fin n → ℂ) → ℂ := fun j z =>
    F j z * u.fr (j 1) (z + b) ^ k / u.fr (j 0) z ^ k *
      cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin n → ℂ))))
  obtain ⟨C, hC⟩ := ThetaGroupFrame.exists_const_of_cover D G
    (fun j => (hV _).inter ((hV _).preimage (by fun_prop)))
    (fun z => by
      obtain ⟨i, hi⟩ := hVc z
      obtain ⟨i', hi'⟩ := hVc (z + b)
      exact ⟨![i, i'], hi, hi'⟩)
    (fun j => by
      have d0 : DifferentiableOn ℂ (u.fr (j 0)) (D j) := (u.fr_hol _).mono Set.inter_subset_left
      have d1 : DifferentiableOn ℂ (fun z => u.fr (j 1) (z + b)) (D j) :=
        (u.fr_hol (j 1)).comp (f := fun z => z + b) (by fun_prop) (fun z hz => hz.2)
      have d2 : DifferentiableOn ℂ (fun z => F j z * u.fr (j 1) (z + b) ^ k * (u.fr (j 0) z ^ k)⁻¹)
          (D j) := ((hF j).mul (d1.pow k)).mul
        ((d0.pow k).inv (fun z hz => pow_ne_zero _ (u.fr_ne _ _ hz.1)))
      refine DifferentiableOn.mul d2 ?_
      refine Differentiable.differentiableOn ?_
      unfold dotProduct
      fun_prop)
    (fun j j' z hz hz' => by
      have e := ThetaGroupFrame.valAt'_gen_two hv L _ _ k θ.φ θ.isGen _ _ _ (h₀ z) (h₁ z) j j' hz.1 hz.2
        hz'.1 hz'.2
      have c0 := u.fr_compat _ _ z (ThetaGroupFrame.top_le_inf _ hz.1 hz'.1)
      have c1 := u.fr_compat _ _ (z + b) (ThetaGroupFrame.top_le_inf _ hz.2 hz'.2)
      have n0 := ThetaGroupFrame.valAt'_unit_ne_zero hv _ _ (ThetaGroupFrame.top_le_inf _ hz.1 hz'.1)
        (L.g (j 0) (j' 0))
      have n1 := ThetaGroupFrame.valAt'_unit_ne_zero hv _ _ (ThetaGroupFrame.top_le_inf _ hz.2 hz'.2)
        (L.g (j 1) (j' 1))
      have n2 := u.fr_ne _ _ hz'.1
      have e' : F j z = _ * F j' z := e
      simp only [G]
      rw [e', c0, c1]
      generalize valAt' (u.ex z).left _ (L.g (j 0) (j' 0)).val = g0 at *
      generalize valAt' (u.ex (z + b)).left _ (L.g (j 1) (j' 1)).val = g1 at *
      field_simp
      ring)
    u.full
    (fun j z hz l hlm => by
      have m0 : z + l ∈ V (j 0) := by
        change ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _
        rw [hl z l hlm]; exact hz.1
      have m1 : z + l + b ∈ V (j 1) := by
        change ⊤ ≤ (u.ex (z + l + b)).left ⁻¹ᵁ _
        rw [hl' z l hlm]; exact hz.2
      refine ⟨⟨m0, m1⟩, ?_⟩
      have eF : F j (z + l) = F j z := by simp only [F]; rw [hl z l hlm]
      have f0 := hfr ⟨l, hlm⟩ _ z hz.1
      have f1 := hfr ⟨l, hlm⟩ _ (z + b) hz.2
      have nχ : χ ⟨l, hlm⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hlm⟩
      have n0 := u.fr_ne _ _ m0
      obtain ⟨N, hN⟩ := hint ⟨l, hlm⟩ a
      have ee := ThetaGroupFrame.exp_herm_eq hH l a N hN
      have eb : cexp (Real.pi * (b ⬝ᵥ Hm.mulVec (star l))) ^ k =
          cexp (Real.pi * ((a : Fin n → ℂ) ⬝ᵥ Hm.mulVec (star l))) := by
        rw [← Complex.exp_nat_mul, hb, smul_dotProduct, smul_eq_mul]
        congr 1
        field_simp
      simp only [G]
      rw [eF, f0, f1, add_right_comm z l b]
      simp only [add_dotProduct, mul_add, Complex.exp_add, mul_pow, ee, eb]
      field_simp)
  refine ⟨C, fun j z hz hz' => ?_⟩
  have h := hC j z ⟨hz, hz'⟩
  have n0 := u.fr_ne _ _ hz
  rw [← h, Complex.exp_neg]
  simp only [G, F]
  field_simp

open GlobalTheory.WeilExp in

theorem weilIs_exp_riemannForm : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  intro A _ _ hA L hL n u Hm χ hAH k a₀ b₀ c hk ha hb hc p₀
  obtain ⟨a, rfl⟩ : ∃ a : u.Λ, (a : Fin n → ℂ) = a₀ := ⟨⟨a₀, ha⟩, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : u.Λ, (b : Fin n → ℂ) = b₀ := ⟨⟨b₀, hb⟩, rfl⟩
  have hv := GlobalTheory.valAt'_rules
  have hext := GlobalTheory.eq_of_valAt'_eq hv GlobalTheory.existsUnique_point_of_ringHom
  have hred := GlobalTheory.isReduced_of_smooth_complex
  have := hA.smooth
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have hpow : ∀ (m : ℕ) w, u.ex w ^ m = u.ex ((m : ℂ) • w) := by
    intro m w
    induction m with
    | zero => simp [hex0]
    | succ m ih => rw [pow_succ, ih, ← u.ex_add, Nat.cast_succ, add_smul, one_smul]
  have htor : ∀ l : u.Λ, u.ex ((k : ℂ)⁻¹ • (l : Fin n → ℂ)) ^ k = 1 := by
    intro l
    rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact (u.ker _).2 l.2
  obtain ⟨E, hE⟩ := im_hermForm_int hL u hAH a b
  have hcE : (c : ℂ) = cexp (-(2 * Real.pi * Complex.I) * (E : ℂ) / k) := by
    rw [hc, ← hE, Complex.ofReal_intCast]
  refine ⟨⊤, trivial, ?_, fun θx θy hx hy => ?_⟩
  · obtain ⟨θx, hx⟩ := exists_thetaGrp A hA L hL k _ (htor a)
    obtain ⟨θy, hy⟩ := exists_thetaGrp A hA L hL k _ (htor b)
    exact ⟨θx, θy, hx, hy⟩
  intro j j' _ _ hjj
  have hsm : Smooth (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens) ⊗ A).hom := by
    rw [← Over.w (fst (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)) A)]
    have h1 : Smooth (fst (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)) A).left := by
      show Smooth (pullback.fst (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)).hom A.hom)
      infer_instance
    have h2 : Smooth (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)).hom := by
      show Smooth ((⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens).ι ≫ 𝟙 _)
      infer_instance
    infer_instance
  apply Units.ext
  refine hext (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens) ⊗ A) (hred _ _ hsm) inferInstance _ _ _
    fun x hxU => ?_
  have hxj := hxU.trans (x.left.preimage_mono inf_le_left)
  have hxj' := hxU.trans (x.left.preimage_mono inf_le_right)
  refine (val_res hv _ _ _ hxU).trans (Eq.trans ?_ (val_res hv _ _ _ hxU).symm)
  obtain ⟨z, hz⟩ := u.ex_onto (x ≫ snd _ _)
  obtain ⟨p, rfl⟩ : ∃ p, x = lift p (u.ex z) := ⟨x ≫ fst _ _, by rw [hz]; ext <;> simp⟩
  have hp : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, p ≫ Out.overResι (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens) ≫ y = y := by
    intro y
    rw [← Category.assoc, Subsingleton.elim (p ≫ Out.overResι _) (𝟙 _), Category.id_comp]
  have hpx : p ≫ θx.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin n → ℂ)) := by rw [hx, hp]
  have hpy : p ≫ θy.pt = u.ex ((k : ℂ)⁻¹ • (b : Fin n → ℂ)) := by rw [hy, hp]
  obtain ⟨Ca, hCa⟩ := thetaGrp_in_frame hL u hAH k a hk _ p θx hpx
  obtain ⟨Cb, hCb⟩ := thetaGrp_in_frame hL u hAH k b hk _ p θy hpy
  have tr : ∀ (θ : Out.ThetaGrp A L k (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens))) (v : Fin n → ℂ),
      p ≫ θ.pt = u.ex v → ∀ w,
      (lift p (u.ex w)).left ≫ (Out.translT A θ.pt).left = (lift p (u.ex (w + v))).left ∧
      (lift p (u.ex w)).left ≫ (Out.translPt A θ.pt).left = (u.ex (w + v)).left := by
    intro θ v h w
    rw [← Over.comp_left, ← Over.comp_left, lift_translT, lift_translPt, h, ← u.ex_add, add_comm v w]
    exact ⟨rfl, rfl⟩
  have sn : ∀ w, (lift p (u.ex w)).left ≫ (snd (Out.overRes (⊤ : (𝟙_ (Over (Sp ℂ))).left.Opens)) A).left =
      (u.ex w).left := by
    intro w
    rw [← Over.comp_left, lift_snd]
  have m := (le_wchart_iff _ _ _ _).1 hxj
  have m' := (le_wchart_iff _ _ _ _).1 hxj'
  have m₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j (.inl 0)) := by
    rw [← sn]; exact m (.inl 0)
  have m₂ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin n → ℂ))).left ⁻¹ᵁ L.U (j (.inl 1)) := by
    rw [← (tr θx _ hpx z).2]; exact m (.inl 1)
  have m₃ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (b : Fin n → ℂ))).left ⁻¹ᵁ L.U (j' (.inl (.inl 1))) := by
    rw [← (tr θy _ hpy z).2]; exact m' (.inl (.inl 1))
  have m₄ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin n → ℂ) + (k : ℂ)⁻¹ • (b : Fin n → ℂ))).left ⁻¹ᵁ
      L.U (j (.inr 1)) := by
    rw [← (tr θy _ hpy _).2, ← (tr θx _ hpx z).1, Category.assoc]; exact m (.inr 1)
  have e₁ : j (.inl 0) = j' (.inl (.inl 0)) := hjj _ _ rfl
  have e₂ : j (.inl 1) = j (.inr 0) := ‹LB.Coh L _ j› _ _ (translT_snd θx.pt).symm
  have e₃ : j' (.inl (.inl 1)) = j' (.inl (.inr 0)) := ‹LB.Coh L _ j'› _ _ (translT_snd θy.pt).symm
  have e₄ : j (.inr 1) = j' (.inl (.inr 1)) := hjj _ _ (translT_translPt_comm θx.pt θy.pt)
  have ec : z + (k : ℂ)⁻¹ • (b : Fin n → ℂ) + (k : ℂ)⁻¹ • (a : Fin n → ℂ) =
      z + (k : ℂ)⁻¹ • (a : Fin n → ℂ) + (k : ℂ)⁻¹ • (b : Fin n → ℂ) := add_right_comm _ _ _
  have h₁ := hCa (j ∘ Sum.inl) z m₁ m₂
  have h₂ := hCb (j ∘ Sum.inr) _ (e₂ ▸ m₂ :) m₄
  have h₃ := hCb ((j' ∘ Sum.inl) ∘ Sum.inl) z (e₁ ▸ m₁ :) m₃
  have h₄ := hCa ((j' ∘ Sum.inl) ∘ Sum.inr) _ (e₃ ▸ m₃ :) (by rw [ec]; exact (e₄ ▸ m₄ :))
  simp only [Function.comp_apply] at h₁ h₂ h₃ h₄
  rw [← e₂] at h₂
  rw [← e₁] at h₃
  rw [← e₃, ← e₄, ec] at h₄
  have key := cancel_frames (pow_ne_zero k (u.fr_ne _ _ m₂)) (pow_ne_zero k (u.fr_ne _ _ m₃))
    (pow_ne_zero k (u.fr_ne _ _ m₄)) h₁ h₂ h₃ h₄
    (by rw [hcE]; exact exp_comm Hm hAH.1 k a b z E hE : _ = _ * _ * (c : ℂ))
  have n₁ := (le_wchart_iff _ _ (j ∘ Sum.inr) _).2 fun i => m (.inr i)
  have n₂ := (le_wchart_iff _ _ (j' ∘ Sum.inl) _).2 fun i => m' (.inl i)
  have n₃ := (le_wchart_iff _ _ ((j' ∘ Sum.inl) ∘ Sum.inr) _).2 fun i => m' (.inl (.inr i))
  refine (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj).trans (Eq.trans ?_ (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj').symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (val_mulGen hv _ _ _ _ _ _ _ _ _ n₂)
    (val_constGen hv L ⊤ c _ _)).symm
  refine (congrArg (_ * ·) (val_pullGen hv _ _ _ _ _ _ _ n₁)).trans
    (Eq.trans ?_ (congrArg (_ * · * (c : ℂ)) (val_pullGen hv _ _ _ _ _ _ _ n₃).symm))
  rw [(tr θx _ hpx z).1, (tr θy _ hpy z).1]
  exact key

end GlobalTheory.AHWeilAny
