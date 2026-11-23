import Mathlib
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictValCPf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Matrix MeasureTheory MvPolynomial
open Formalism.REAL (fockF)
open scoped ComplexOrder

namespace GlobalTheory.ValSchur

theorem fockF_swap {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by
  classical
  rw [Formalism.L2.Col.fockF_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.Col.fockF_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]
  ring

theorem fockF_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : ∃ r : ℝ, 0 < r ∧ fockF f f = (r : ℂ) := by
  refine ⟨∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_) (support_nonempty.2 hf)
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  · unfold fockF
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_mul, Complex.ofReal_natCast]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem nfAll_swap (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p q = star (nfAll lam q p) := by
  unfold nfAll
  rw [star_div₀, star_prod, ← fockF_swap]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => fockF_swap _ _

theorem nfAll_pos (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ} (hp : p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ nfAll lam p p = (r : ℂ) := by
  obtain ⟨r, hr, e⟩ := fockF_pos hp
  choose s hs es using fun τ => fockF_pos (f := extremal ℂ n (lam τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (lam τ).natW)
  refine ⟨r / ∏ τ, s τ, div_pos hr (Finset.prod_pos fun τ _ => hs τ), ?_⟩
  unfold nfAll
  rw [e, Complex.ofReal_div, Complex.ofReal_prod]
  simp only [es]

variable {G : ι → Matrix (Fin n) (Fin n) ℂ}

theorem tr_mem (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    {v : Frames G → ℂ} (hv : v ∈ ValC G lam) : (fun z => v (Frames.tr g hg z)) ∈ ValC G lam :=
  Formalism.MainNotions.Ext.Lw.valC_tr G lam g hg hv

theorem isUnit_inv {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (τ : ι) : IsUnit ((g τ)⁻¹).det := by
  rw [det_nonsing_inv]; exact (hg τ).ringInverse

omit [Fintype ι] in
theorem tr_tr_inv {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (hg' : ∀ τ, IsUnit ((g τ)⁻¹).det)
    (z : Frames G) : Frames.tr g hg (Frames.tr (fun τ => (g τ)⁻¹) hg' z) = z :=
  Subtype.ext (funext fun τ => by
    show g τ * ((g τ)⁻¹ * z.1 τ) = z.1 τ
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hg τ), Matrix.one_mul])

omit [Fintype ι] in
theorem tr_inv_tr {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (hg' : ∀ τ, IsUnit ((g τ)⁻¹).det)
    (z : Frames G) : Frames.tr (fun τ => (g τ)⁻¹) hg' (Frames.tr g hg z) = z :=
  Subtype.ext (funext fun τ => by
    show (g τ)⁻¹ * (g τ * z.1 τ) = z.1 τ
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hg τ), Matrix.one_mul])

theorem fnOf_tr (s : ι → ℤ) (M g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (z : Frames G) :
    fnOf G s M P (Frames.tr g hg z) = fnOf G s (fun τ => M τ * g τ) P z := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, Matrix.mul_assoc]

theorem exists_coord (lam : ι → DomWeight n) (o : Frames G) {v : Frames G → ℂ} (hv : v ∈ ValC G lam) :
    ∃ P ∈ CSpan lam, v = fnOf G (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P := by
  obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 (tr_mem lam o.1 o.2 hv)
  refine ⟨P, hP, funext fun z => ?_⟩
  have h := congrFun e (Frames.tr (fun τ => (o.1 τ)⁻¹) (isUnit_inv o.2) z)
  simp only [tr_tr_inv, fnOf_tr, Pi.one_apply, Matrix.one_mul] at h
  exact h.symm

omit [Fintype ι] in
theorem unit_of_unitary (hG : ∀ τ, (G τ).PosDef) {g : ι → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ τ, (g τ)ᴴ * G τ * g τ = G τ) (τ : ι) :
    IsUnit (g τ).det := by
  have h := congrArg Matrix.det (hu τ)
  rw [det_mul] at h
  have h2 : IsUnit (G τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hG τ).isUnit
  rw [← h] at h2
  exact isUnit_of_mul_isUnit_right h2

omit [Fintype ι] in
theorem inv_unitary {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (hu : ∀ τ, (g τ)ᴴ * G τ * g τ = G τ) (τ : ι) :
    ((g τ)⁻¹)ᴴ * G τ * (g τ)⁻¹ = G τ := by
  conv_lhs => rw [← hu τ]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ (hg τ), conjTranspose_one,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hg τ), Matrix.mul_one]

omit [Fintype ι] in
theorem exists_isON (hG : ∀ τ, (G τ).PosDef) : ∃ o : Frames G, o.IsON := by
  have h : ∀ τ, ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ G τ = Bᴴ * B := fun τ => by
    open scoped MatrixOrder in
    obtain ⟨B, hB, e⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 (hG τ).isStrictlyPositive
    exact ⟨B, (Matrix.isUnit_iff_isUnit_det _).1 hB, e⟩
  choose B hu hJ using h
  refine ⟨⟨fun τ => (B τ)⁻¹, fun τ => ?_⟩, fun τ => Or.inl ?_⟩
  · rw [det_nonsing_inv]; exact (hu τ).ringInverse
  · show ((B τ)⁻¹)ᴴ * G τ * (B τ)⁻¹ = 1
    rw [hJ τ, conjTranspose_nonsing_inv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [det_conjTranspose]; exact (hu τ).star), Matrix.one_mul, Matrix.mul_nonsing_inv _ (hu τ)]

def IsFock (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (ip : (Frames G → ℂ) → (Frames G → ℂ) → ℂ) : Prop :=
  ∀ o : Frames G, o.IsON → ∀ P ∈ CSpan lam, ∀ Q ∈ CSpan lam,
    ip (fnOf G (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P) (fnOf G (shiftOf lam) (fun τ => (o.1 τ)⁻¹) Q) = nfAll lam Q P

variable {lam : ι → DomWeight n} {ip ip' : (Frames G → ℂ) → (Frames G → ℂ) → ℂ}

theorem IsFock.eq (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) (h' : IsFock G lam ip') {f g : Frames G → ℂ}
    (hf : f ∈ ValC G lam) (hg : g ∈ ValC G lam) : ip f g = ip' f g := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  obtain ⟨Q, hQ, rfl⟩ := exists_coord lam o hg
  rw [h o ho P hP Q hQ, h' o ho P hP Q hQ]

theorem IsFock.swap (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) {f g : Frames G → ℂ}
    (hf : f ∈ ValC G lam) (hg : g ∈ ValC G lam) : ip g f = star (ip f g) := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  obtain ⟨Q, hQ, rfl⟩ := exists_coord lam o hg
  rw [h o ho P hP Q hQ, h o ho Q hQ P hP, nfAll_swap]

theorem IsFock.pos (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) {f : Frames G → ℂ}
    (hf : f ∈ ValC G lam) (h0 : f ≠ 0) : ∃ r : ℝ, 0 < r ∧ ip f f = (r : ℂ) := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  rw [h o ho P hP P hP]
  exact nfAll_pos lam fun e => h0 (by rw [e, map_zero])

theorem IsFock.tr (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) {k : ι → Matrix (Fin n) (Fin n) ℂ} (hk : ∀ τ, IsUnit (k τ).det)
    (hu : ∀ τ, (k τ)ᴴ * G τ * k τ = G τ) {f g : Frames G → ℂ} (hf : f ∈ ValC G lam) (hg : g ∈ ValC G lam) :
    ip (fun z => f (Frames.tr k hk z)) (fun z => g (Frames.tr k hk z)) = ip f g := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  obtain ⟨Q, hQ, rfl⟩ := exists_coord lam o hg
  have ho' := ho.tr (fun τ => (k τ)⁻¹) (isUnit_inv hk) (inv_unitary hk hu)
  have e : (fun τ => ((Frames.tr (fun τ => (k τ)⁻¹) (isUnit_inv hk) o).1 τ)⁻¹) = fun τ => (o.1 τ)⁻¹ * k τ := funext fun τ => by
    show ((k τ)⁻¹ * o.1 τ)⁻¹ = _
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hk τ)]
  have h2 := h _ ho' P hP Q hQ
  rw [e] at h2
  rw [h o ho P hP Q hQ, ← h2]
  simp only [fnOf_tr]

theorem continuous_val {X : Type} [TopologicalSpace X] {m : X → ι → Matrix (Fin n) (Fin n) ℂ} (hm : ∀ x τ, IsUnit (m x τ).det)
    (hc : ∀ τ, Continuous fun x => m x τ) (y : Frames G) {f : Frames G → ℂ} (hf : f ∈ ValC G lam) :
    Continuous fun x => f (Frames.tr (m x) (hm x) y) := by
  obtain ⟨P, -, rfl⟩ := hf
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul]
  refine (continuous_finsetProd _ fun τ _ => ?_).mul ((MvPolynomial.continuous_eval P).comp (continuous_pi fun v => ?_))
  · exact (((hc τ).matrix_mul continuous_const).matrix_det).zpow₀ _ fun x => Or.inl ((Frames.tr (m x) (hm x) y).2 τ).ne_zero
  · exact ((hc v.1).matrix_mul continuous_const).matrix_elem _ _

theorem exists_val_ne (lam : ι → DomWeight n) (y : Frames G) : ∃ f ∈ ValC G lam, f y ≠ 0 := by
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.Core.Rk.Top.Model.valC_ne_bot G lam)
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  have hu : ∀ τ, IsUnit (z.1 τ * (y.1 τ)⁻¹).det := fun τ => by
    rw [det_mul]; exact (z.2 τ).mul (isUnit_inv y.2 τ)
  refine ⟨_, tr_mem lam _ hu hf, ?_⟩
  have e : Frames.tr _ hu y = z := Subtype.ext (funext fun τ => by
    show z.1 τ * (y.1 τ)⁻¹ * y.1 τ = z.1 τ
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (y.2 τ), Matrix.mul_one])
  simp only [e]
  exact hz

def IsSesq (ip : (Frames G → ℂ) → (Frames G → ℂ) → ℂ) : Prop :=
  (∀ (a : ℂ) (f f' g : Frames G → ℂ), ip (a • f + f') g = star a * ip f g + ip f' g) ∧
    ∀ (a : ℂ) (f g g' : Frames G → ℂ), ip f (a • g + g') = a * ip f g + ip f g'

theorem avg_eq (hG : ∀ τ, (G τ).PosDef) (lam : ι → DomWeight n) {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (m : K → ι → Matrix (Fin n) (Fin n) ℂ) (hm : ∀ k τ, IsUnit (m k τ).det) (hc : ∀ τ, Continuous fun k => m k τ)
    (hmul : ∀ a b τ, m (a * b) τ = m a τ * m b τ)
    (hs : ∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) → ∃ k, ∀ τ, m k τ = g τ) (y : Frames G) :
    ∃ c : ℝ, 0 < c ∧ ∀ ip, IsFock G lam ip → IsSesq ip → ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam,
      ∫ k, g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y)) ∂ν = (c : ℂ) * ip f g := by
  by_cases hex : ∃ ip, IsFock G lam ip ∧ IsSesq ip
  swap
  · exact ⟨1, one_pos, fun ip h1 h2 => absurd ⟨ip, h1, h2⟩ hex⟩
  obtain ⟨ip, hF, hS⟩ := hex
  set Φ : (Frames G → ℂ) → (Frames G → ℂ) → ℂ := fun f g =>
    ∫ k, g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y)) ∂ν with hΦ
  have hcont : ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam,
      Continuous fun k => g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y)) := fun f hf g hg =>
    (continuous_val hm hc y hg).mul (continuous_val hm hc y hf).star
  have hint : ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam,
      Integrable (fun k => g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y))) ν := fun f hf g hg =>
    integrableOn_univ.1 ((hcont f hf g hg).continuousOn.integrableOn_compact isCompact_univ)
  have Φl : ∀ (a : ℂ) (f f' g : Frames G → ℂ), f ∈ ValC G lam → f' ∈ ValC G lam → g ∈ ValC G lam →
      Φ (a • f + f') g = star a * Φ f g + Φ f' g := fun a f f' g hf hf' hg => by
    simp only [hΦ]
    rw [← integral_const_mul, ← integral_add ((hint f hf g hg).const_mul _) (hint f' hf' g hg)]
    congr 1; funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul']
    ring
  have Φr : ∀ (a : ℂ) (f g g' : Frames G → ℂ), f ∈ ValC G lam → g ∈ ValC G lam → g' ∈ ValC G lam →
      Φ f (a • g + g') = a * Φ f g + Φ f g' := fun a f g g' hf hg hg' => by
    simp only [hΦ]
    rw [← integral_const_mul, ← integral_add ((hint f hf g hg).const_mul _) (hint f hf g' hg')]
    congr 1; funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Φtr : ∀ (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det), (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) →
      ∀ f f', Φ (fun z => f (Frames.tr g hg z)) (fun z => f' (Frames.tr g hg z)) = Φ f f' := fun g hg hu f f' => by
    obtain ⟨k0, hk0⟩ := hs g hu
    have e : ∀ k, Frames.tr g hg (Frames.tr (m k) (hm k) y) = Frames.tr (m (k0 * k)) (hm _) y := fun k =>
      Subtype.ext (funext fun τ => by
        show g τ * (m k τ * y.1 τ) = m (k0 * k) τ * y.1 τ
        rw [hmul, hk0, Matrix.mul_assoc])
    simp only [hΦ, e]
    exact integral_mul_left_eq_self (fun k => f' (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y))) k0
  obtain ⟨c, e, he, he0, hce⟩ := (GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space (Frames G) (ValC G lam) inferInstance ip Φ
    (fun a f f' g _ _ _ => hS.1 a f f' g) (fun a f g g' _ _ _ => hS.2 a f g g') (fun f g hf hg => hF.swap hG hf hg)
    (fun f hf h0 => by obtain ⟨r, hr, er⟩ := hF.pos hG hf h0; rw [er]; exact hr) Φl Φr).2
    (GlobalTheory.Core.Rk.Top.Model.valC_ne_bot G lam)
  obtain ⟨-, -, ia, is⟩ := GlobalTheory.sesq_rules_of_combination (ValC G lam) ip (fun a f f' g _ _ _ => hS.1 a f f' g)
    (fun a f g g' _ _ _ => hS.2 a f g g')
  obtain ⟨-, -, pa, ps⟩ := GlobalTheory.sesq_rules_of_combination (ValC G lam) Φ Φl Φr
  let W : Submodule ℂ (Frames G → ℂ) :=
    { carrier := {g | g ∈ ValC G lam ∧ ∀ f ∈ ValC G lam, Φ f g = c * ip f g}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun f hf => by
        rw [pa f a b hf ha.1 hb.1, ia f a b hf ha.1 hb.1, ha.2 f hf, hb.2 f hf, mul_add]⟩
      zero_mem' := ⟨zero_mem _, fun f hf => by
        have h1 := ps 0 f 0 hf (zero_mem _)
        have h2 := is 0 f 0 hf (zero_mem _)
        rw [zero_smul, zero_mul] at h1 h2
        rw [h1, h2, mul_zero]⟩
      smul_mem' := fun a b hb => ⟨Submodule.smul_mem _ _ hb.1, fun f hf => by
        rw [ps a f b hf hb.1, is a f b hf hb.1, hb.2 f hf]; ring⟩ }
  have hW : W = ValC G lam := by
    refine Formalism.L2.SG.Pf.valuation_character_irreducible ι n G (fun τ => Or.inl (hG τ)) lam W (fun g hg => hg.1) ?_ ?_
    · exact (Submodule.ne_bot_iff _).2 ⟨e, ⟨he, hce⟩, he0⟩
    · intro g hu F hFW
      have hg := unit_of_unitary hG hu
      refine ⟨fun z => F (Frames.tr g hg z), ⟨tr_mem lam g hg hFW.1, fun f hf => ?_⟩, fun z z' hz => ?_⟩
      · have hf' := tr_mem lam _ (isUnit_inv hg) hf
        have ef : f = fun z => (fun z => f (Frames.tr (fun τ => (g τ)⁻¹) (isUnit_inv hg) z)) (Frames.tr g hg z) :=
          funext fun z => by simp only [tr_inv_tr]
        have a1 := Φtr g hg hu (fun z => f (Frames.tr (fun τ => (g τ)⁻¹) (isUnit_inv hg) z)) F
        have a2 := hF.tr hG hg hu hf' hFW.1
        rw [← ef] at a1 a2
        exact a1.trans ((hFW.2 _ hf').trans (congrArg (c * ·) a2.symm))
      · exact congrArg F (Subtype.ext (funext fun τ => (hz τ).symm))
  have hall : ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam, Φ f g = c * ip f g := fun f hf g hg =>
    (show g ∈ W from hW ▸ hg).2 f hf
  obtain ⟨f0, hf0, hy⟩ := exists_val_ne lam y
  obtain ⟨r, hr, er⟩ := hF.pos hG hf0 (fun h => hy (by rw [h]; rfl))
  have h1 : ∀ τ, m 1 τ = 1 := fun τ => by
    have := hmul 1 1 τ
    rw [mul_one] at this
    calc m 1 τ = (m 1 τ)⁻¹ * (m 1 τ * m 1 τ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm 1 τ), Matrix.one_mul]
      _ = 1 := by rw [← this, Matrix.nonsing_inv_mul _ (hm 1 τ)]
  have hcn : Continuous fun k => Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) :=
    Complex.continuous_normSq.comp (continuous_val hm hc y hf0)
  have hpos : 0 < ∫ k, Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) ∂ν := by
    refine hcn.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      (fun k => Complex.normSq_nonneg _) (x := 1) ?_
    have e1 : Frames.tr (m 1) (hm 1) y = y := Subtype.ext (funext fun τ => by
      show m 1 τ * y.1 τ = y.1 τ
      rw [h1, Matrix.one_mul])
    rw [e1]
    exact (Complex.normSq_pos.2 hy).ne'
  have hΦ0 : Φ f0 f0 = ((∫ k, Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) ∂ν : ℝ) : ℂ) := by
    simp only [hΦ, Complex.star_def, Complex.mul_conj]
    exact integral_ofReal
  have hc0 := hall f0 hf0 f0 hf0
  rw [hΦ0, er] at hc0
  refine ⟨(∫ k, Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) ∂ν) / r, div_pos hpos hr, fun ip' hF' _ f hf g hg => ?_⟩
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [Complex.ofReal_div, hc0, mul_div_cancel_right₀ _ hr', hF'.eq hG hF hf hg]
  exact hall f hf g hg

end GlobalTheory.ValSchur
