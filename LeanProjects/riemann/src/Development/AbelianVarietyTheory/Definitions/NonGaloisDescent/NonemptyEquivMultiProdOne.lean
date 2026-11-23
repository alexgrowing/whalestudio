import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Invariance

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

def parIndEquiv (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {σ : Representation ℂ (Levi k m) W}
    (φ : ρ.Equiv σ) : (parInd e ρ).Equiv (parInd e σ) :=
  equivOfBijective (parIndMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨parIndMap e φ.symm.toIntertwiningMap,
      fun f => Subtype.ext (Subtype.ext (funext fun x => φ.symm_apply_apply (f.1.1 x))),
      fun f => Subtype.ext (Subtype.ext (funext fun x => φ.apply_symm_apply (f.1.1 x)))⟩)

def multiProdEquiv (e : (Σ a, m a) ≃ n) {X Y : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] {π : ∀ a, Representation ℂ (GL (m a) k) (X a)}
    {σ : ∀ a, Representation ℂ (GL (m a) k) (Y a)} (φ : ∀ a, (π a).Equiv (σ a)) :
    (multiProd e π).Equiv (multiProd e σ) :=
  parIndEquiv e (piTensorEquiv φ)
private theorem twKer_le_comap_intertwining {G : Type} [Group G] {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (f : ρ.IntertwiningMap τ) (N : Subgroup G) :
    twKer ρ N 1 ≤ (twKer τ N 1).comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨u, f v, ?_⟩
  simp [Representation.IntertwiningMap.isIntertwining _ _ f]

theorem isCuspidal_of_equiv {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W} (φ : π.Equiv σ)
    (h : IsCuspidal π) : IsCuspidal σ := by
  refine ⟨fun w => ?_, fun s d e hne => ?_⟩
  · have key : ∀ g, φ.symm (σ g w) = π g (φ.symm w) := fun g =>
      Representation.IntertwiningMap.isIntertwining _ _ φ.symm.toIntertwiningMap g w
    have hset : {g : GL n k | σ g w = w} = {g | π g (φ.symm w) = φ.symm w} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hg
        rw [← key, hg]
      · intro hg
        apply EquivLike.injective φ.symm
        rw [key, hg]
    rw [hset]
    exact h.1 _
  · have h2 : twKer π (unipRad k e) 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne)
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    have hw := twKer_le_comap_intertwining φ.toIntertwiningMap (unipRad k e) (h2 ▸ Submodule.mem_top : φ.symm w ∈ twKer π (unipRad k e) 1)
    rw [Submodule.mem_comap] at hw
    simpa using hw

theorem isCuspidal_twist {π : Representation ℂ (GL n k) V} (h : IsCuspidal π) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsCuspidal (twist π (detChar n χ)) := by
  refine ⟨isSmooth_twist h.1 hχ.detChar, fun s d e hne => ?_⟩
  have h2 : twKer π (unipRad k e) 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne)
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 ?_)
  rw [← h2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, v, ?_⟩
  simp [twist_apply, detChar_apply, det_eq_one_of_mem_unipRad k u.2]

theorem isSmoothChar_absPow (s : ℂ) : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)

theorem absPow_ofReal_eq_one {s : ℝ} : absPow k s = 1 ↔ s = 0 := by
  constructor
  · intro h
    obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
    have h1 : ((absPow k (s : ℂ) ϖ : ℂˣ) : ℂ) = 1 := by rw [h]; rfl
    rw [val_absPow_ofReal, Complex.ofReal_eq_one] at h1
    have hpos : 0 < nabs k ϖ := nabs_pos' k ϖ
    have hne : nabs k ϖ ≠ 1 := by
      rw [Ne, nabs_eq_one_iff, hϖ]
      exact ne_of_lt uniformizer_lt_one
    rw [Real.rpow_def_of_pos hpos, Real.exp_eq_one_iff, mul_eq_zero] at h1
    exact h1.resolve_left (Real.log_ne_zero_of_pos_of_ne_one hpos hne)
  · rintro rfl
    simp
private theorem ofChar_cl_congr (e : (Σ _ : Fin 1, n) ≃ n) (g : GL n k) : g ∈ parab k e := by
  rw [mem_parab]
  intro i j hij
  exact absurd hij (by rw [Subsingleton.elim (blk e j) (blk e i)]; exact lt_irrefl _)
private theorem leviProj_fin_one (e : (Σ _ : Fin 1, n) ≃ n) (he : ∀ a i, e ⟨a, i⟩ = i) (p : parab k e) (a : Fin 1) :
    leviProj k e p a = (p : GL n k) :=
  Matrix.GeneralLinearGroup.ext fun i j => by rw [leviProj_apply, he, he]
private theorem deltaHalf_fin_one_eq_one (g : Levi k fun _ : Fin 1 => n) : deltaHalf k (fun _ : Fin 1 => n) g = 1 := by
  have h0 : ∀ a : Fin 1, modExp (fun _ : Fin 1 => n) a = 0 := by
    intro a
    rw [Subsingleton.elim a 0]
    simp [modExp]
  ext
  simp [deltaHalf_apply, h0]

theorem nonempty_equiv_multiProd_one {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (e : (Σ _ : Fin 1, n) ≃ n)
    (he : ∀ a i, e ⟨a, i⟩ = i) : Nonempty (π.Equiv (multiProd e fun _ : Fin 1 => π)) := by
  classical
  let ι : V ≃ₗ[ℂ] PiTensorProduct ℂ (fun _ : Fin 1 => V) := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).symm
  have hι : ∀ v, ι v = PiTensorProduct.tprod ℂ (fun _ => v) := fun v =>
    PiTensorProduct.subsingletonEquiv_symm_apply' 0 v
  let σ' := (twist (piTensor fun _ : Fin 1 => π) (deltaHalf k fun _ : Fin 1 => n)).comp (leviProj k e)
  have hact : ∀ (p : parab k e) (v : V), σ' p (ι v) = ι (π p v) := by
    intro p v
    simp only [σ', MonoidHom.comp_apply, twist_apply, deltaHalf_fin_one_eq_one, hι, piTensor_tprod, leviProj_fin_one e he]
    simp
  let G0 : V → indSpace (parab k e) σ' := fun v => ⟨fun g => ι (π g v), fun p g => by
    show ι (π (↑p * g) v) = σ' p (ι (π g v))
    rw [map_mul, Module.End.mul_apply, hact]⟩
  have hopen : ∀ v, G0 v ∈ smoothPart (ind (parab k e) σ') := by
    intro v
    show IsOpen {g | ind (parab k e) σ' g (G0 v) = G0 v}
    convert hπ v using 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have h1 := congrArg (fun f : indSpace (parab k e) σ' => f.1 1) h
      have h2 : ι (π (1 * g) v) = ι (π 1 v) := h1
      rw [one_mul, map_one, Module.End.one_apply] at h2
      exact ι.injective h2
    · intro h
      apply Subtype.ext
      funext y
      show ι (π (y * g) v) = ι (π y v)
      rw [map_mul, Module.End.mul_apply, h]
  let F : V →ₗ[ℂ] IndSp e (piTensor fun _ : Fin 1 => π) :=
    { toFun := fun v => ⟨G0 v, hopen v⟩
      map_add' := fun v w => by
        apply Subtype.ext
        apply Subtype.ext
        funext g
        simp [G0]
      map_smul' := fun c v => by
        apply Subtype.ext
        apply Subtype.ext
        funext g
        simp [G0] }
  let Φ : π.IntertwiningMap (multiProd e fun _ : Fin 1 => π) :=
    ⟨F, fun g => LinearMap.ext fun v => by
      apply Subtype.ext
      apply Subtype.ext
      funext y
      show ι (π y (π g v)) = ι (π (y * g) v)
      rw [map_mul, Module.End.mul_apply]⟩
  have hinj : Function.Injective Φ := fun v w h => by
    have h1 := congrArg (fun f : IndSp e (piTensor fun _ : Fin 1 => π) => f.1.1 1) h
    have h2 : ι (π 1 v) = ι (π 1 w) := h1
    simpa using h2
  have hsurj : Function.Surjective Φ := fun f => by
    refine ⟨ι.symm (f.1.1 1), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext y
    have hl := f.1.2 ⟨y, ofChar_cl_congr e y⟩ 1
    rw [mul_one] at hl
    have h3 := hact ⟨y, ofChar_cl_congr e y⟩ (ι.symm (f.1.1 1))
    rw [LinearEquiv.apply_symm_apply] at h3
    exact h3.symm.trans hl.symm
  exact ⟨equivOfBijective Φ ⟨hinj, hsurj⟩⟩

end Invariance

variable (k) in

abbrev IrrGL : Type 1 := Σ n : ℕ, IrrCl (GL (Fin n) k)

namespace IrrGL

abbrev rep (x : IrrGL k) : Representation ℂ (GL (Fin x.1) k) x.2.rep.V := x.2.rep.ρ

def of {N : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : IrrGL k :=
  ⟨N, (⟨V, π, hs, hi⟩ : IrrRep _).cl⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem of_eq_of {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {hs : IsSmooth π} {hi : π.IsIrreducible}
    {σ : Representation ℂ (GL (Fin N) k) W} {hs' : IsSmooth σ} {hi' : σ.IsIrreducible} :
    of π hs hi = of σ hs' hi' ↔ Nonempty (π.Equiv σ) := by
  simp only [IrrGL.of, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  exact IrrRep.cl_eq_iff

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

@[simp] theorem of_rep (x : IrrGL k) : of x.rep x.2.rep.smooth x.2.rep.irr = x := Sigma.ext rfl (heq_of_eq (IrrCl.cl_rep _))

def equivOf {N : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    π.Equiv (of π hs hi).rep := equivRep ⟨V, π, hs, hi⟩

def tw (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : IrrGL k :=
  ⟨x.1, clTwist x.2 (detChar _ χ) hχ.detChar⟩

def nu (x : IrrGL k) (s : ℂ) : IrrGL k := x.tw (absPow k s) (isSmoothChar_absPow s)

def ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : IrrGL k := ⟨1, (IrrRep.det (Fin 1) χ hχ).cl⟩

def IsCusp (x : IrrGL k) : Prop := 0 < x.1 ∧ IsCuspidal x.rep

def Inert (x y : IrrGL k) : Prop := ∃ (μ : kˣ →* ℂˣ) (hμ : IsUnram μ), y = x.tw μ (isSmoothChar_of_isUnram hμ)

def IsUnramChar (x : IrrGL k) : Prop := ∃ (μ : kˣ →* ℂˣ) (hμ : IsUnram μ), x = ofChar μ (isSmoothChar_of_isUnram hμ)

@[simp] theorem tw_fst (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (x.tw χ hχ).1 = x.1 := rfl

@[simp] theorem nu_fst (x : IrrGL k) (s : ℂ) : (x.nu s).1 = x.1 := rfl

def twEquiv (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (twist x.rep (detChar _ χ)).Equiv (x.tw χ hχ).rep := equivRep (irrTwist x.2.rep _ hχ.detChar)

theorem tw_of {N : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (of π hs hi).tw χ hχ =
      of (twist π (detChar _ χ)) (isSmooth_twist hs hχ.detChar) (isIrreducible_twist hi _) := Sigma.ext rfl (heq_of_eq (clTwist_cl _ _ _))
private theorem clTwist_congr {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : IrrCl G)
    {χ ψ : G →* ℂˣ} (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) : clTwist c χ hχ = clTwist c ψ hψ := by
  subst h
  rfl
private theorem detChar_mul' (m : Type) [Fintype m] [DecidableEq m] (χ ψ : kˣ →* ℂˣ) :
    detChar m (χ * ψ) = detChar m χ * detChar m ψ := by
  ext g
  simp [detChar_apply]

theorem tw_tw (x : IrrGL k) (χ ψ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    (x.tw χ hχ).tw ψ hψ = x.tw (χ * ψ) (hχ.mul hψ) := by
  obtain ⟨N, c⟩ := x
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact (clTwist_clTwist _ _ _ _ _).trans (clTwist_congr _ (detChar_mul' _ χ ψ).symm _ _)

theorem tw_one (x : IrrGL k) (h : IsSmoothChar (1 : kˣ →* ℂˣ)) : x.tw 1 h = x := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  show clTwist x.2 _ _ = x.2
  have h1 : detChar (Fin x.1) (1 : kˣ →* ℂˣ) = 1 := by
    ext g
    simp [detChar_apply]
  exact (clTwist_congr _ h1 _ isSmoothChar_one).trans (clTwist_one _ _)
private theorem tw_congr' (x : IrrGL k) {χ ψ : kˣ →* ℂˣ} (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    x.tw χ hχ = x.tw ψ hψ := by
  subst h
  rfl

@[simp] theorem nu_nu (x : IrrGL k) (s t : ℂ) : (x.nu s).nu t = x.nu (s + t) := by
  show (x.tw _ _).tw _ _ = x.tw _ _
  rw [tw_tw]
  exact tw_congr' _ (absPow_add k s t).symm _ _

@[simp] theorem nu_zero (x : IrrGL k) : x.nu 0 = x := (tw_congr' x (absPow_zero k) _ isSmoothChar_one).trans (tw_one x _)
private theorem mem_parab_fin_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ ψ : G →* ℂˣ}
    (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) : (IrrRep.ofChar χ hχ).cl = (IrrRep.ofChar ψ hψ).cl := by
  subst h
  rfl

theorem tw_ofChar (χ ψ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    (ofChar χ hχ).tw ψ hψ = ofChar (χ * ψ) (hχ.mul hψ) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact (clTwist_ofChar _ _ _ _).trans (mem_parab_fin_one (detChar_mul' _ χ ψ).symm _ _)
private theorem det_scalar_fin_one' (x : kˣ) : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) x) = x := by
  ext
  simp

theorem ofChar_inj {χ ψ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} {hψ : IsSmoothChar ψ} :
    ofChar χ hχ = ofChar ψ hψ ↔ χ = ψ := by
  constructor
  · intro h
    simp only [IrrGL.ofChar, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    have h2 := (IrrRep.cl_ofChar_inj _ _).1 h
    ext x
    have h3 := DFunLike.congr_fun h2 (GeneralLinearGroup.scalar (Fin 1) x)
    simp only [detChar_apply] at h3
    rw [det_scalar_fin_one'] at h3
    rw [h3]
  · rintro rfl
    rfl

theorem nu_ofChar_inj (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) {s t : ℝ} :
    (ofChar χ hχ).nu s = (ofChar χ hχ).nu t ↔ s = t := by
  constructor
  · intro h
    simp only [IrrGL.nu, tw_ofChar, ofChar_inj] at h
    have h2 : absPow k (((s - t : ℝ)) : ℂ) = 1 := by
      rw [Complex.ofReal_sub, sub_eq_add_neg, absPow_add, absPow_neg, mul_left_cancel h, mul_inv_cancel]
    exact sub_eq_zero.1 (absPow_ofReal_eq_one.1 h2)
  · rintro rfl
    rfl

theorem isCusp_of {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {hs : IsSmooth π} {hi : π.IsIrreducible} :
    (of π hs hi).IsCusp ↔ 0 < N ∧ IsCuspidal π := by
  show 0 < N ∧ IsCuspidal (of π hs hi).rep ↔ _
  exact and_congr Iff.rfl ⟨fun h => isCuspidal_of_equiv (equivOf π hs hi).symm h,
    fun h => isCuspidal_of_equiv (equivOf π hs hi) h⟩

theorem IsCusp.tw {x : IrrGL k} (h : x.IsCusp) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (x.tw χ hχ).IsCusp := ⟨h.1, isCuspidal_of_equiv (x.twEquiv χ hχ) (isCuspidal_twist h.2 hχ)⟩

theorem IsCusp.nu {x : IrrGL k} (h : x.IsCusp) (s : ℂ) : (x.nu s).IsCusp := h.tw _ _

theorem isCusp_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (ofChar χ hχ).IsCusp := ⟨one_pos, isCuspidal_of_equiv (IrrRep.nonempty_equiv_rep (IrrRep.det (Fin 1) χ hχ)).some.symm
  (isCuspidal_detRep_one hχ)⟩

theorem inert_equivalence : Equivalence (Inert (k := k)) where
  refl x := ⟨1, fun _ _ => rfl, (tw_one x _).symm⟩
  symm := by
    rintro x y ⟨μ, hμ, rfl⟩
    refine ⟨μ⁻¹, isUnram_inv hμ, ?_⟩
    rw [tw_tw]
    exact ((tw_congr' x (mul_inv_cancel μ) _ isSmoothChar_one).trans (tw_one x _)).symm
  trans := by
    rintro x y z ⟨μ, hμ, rfl⟩ ⟨μ', hμ', rfl⟩
    exact ⟨μ * μ', isUnram_mul hμ hμ', tw_tw _ _ _ _ _⟩

theorem inert_nu (x : IrrGL k) (s : ℂ) : Inert x (x.nu s) := ⟨absPow k s, isUnram_absPow k s, rfl⟩

theorem inert_of {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {hs : IsSmooth π} {hi : π.IsIrreducible}
    {σ : Representation ℂ (GL (Fin N) k) W} {hs' : IsSmooth σ} {hi' : σ.IsIrreducible} :
    Inert (of π hs hi) (of σ hs' hi') ↔ InertEquiv π σ := by
  constructor
  · rintro ⟨μ, hμ, h⟩
    rw [tw_of, of_eq_of] at h
    exact ⟨μ, hμ, h⟩
  · rintro ⟨μ, hμ, h⟩
    exact ⟨μ, hμ, by rw [tw_of, of_eq_of]; exact h⟩

end IrrGL

def prodIrr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Representation ℂ (GL (Fin N) k) (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) :=
  multiProd (stdBlocks (fun a => (x a).1) hd) fun a => (x a).rep

theorem isSmooth_prodIrr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) : IsSmooth (prodIrr x hd) := isSmooth_parInd _ _

def prodIrrEquiv {h N : ℕ} {d : Fin h → ℕ} (hd : ∑ a, d a = N) {X : Fin h → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hi : ∀ a, (π a).IsIrreducible) :
    (multiProd (stdBlocks d hd) π).Equiv (prodIrr (fun a => IrrGL.of (π a) (hs a) (hi a)) hd) :=
  multiProdEquiv _ fun a => IrrGL.equivOf (π a) (hs a) (hi a)

theorem nonempty_equiv_prodIrr_one (x : IrrGL k) (hd : ∑ _ : Fin 1, x.1 = x.1) :
    Nonempty (x.rep.Equiv (prodIrr (fun _ : Fin 1 => x) hd)) := nonempty_equiv_multiProd_one x.2.rep.smooth _ fun a i => by
  apply Fin.ext
  rw [stdBlocks_val, Finset.sum_eq_zero fun b _ => absurd b.2 (by simp), zero_add]

def HasSupport {n : Type} [Fintype n] [DecidableEq n] (π : Representation ℂ (GL n k) V) (s : Multiset (IrrGL k)) : Prop :=
  ∃ (h : ℕ) (x : Fin h → IrrGL k), Finset.univ.val.map x = s ∧ IsCuspSupport π (fun a => (x a).1) fun a => (x a).rep

section Support

variable {n : Type} [Fintype n] [DecidableEq n] {π : Representation ℂ (GL n k) V} {s : Multiset (IrrGL k)}

theorem HasSupport.isIrreducible (h : HasSupport π s) : π.IsIrreducible := by
  obtain ⟨_, _, _, hc⟩ := h
  exact hc.1

theorem HasSupport.isSmooth (h : HasSupport π s) : IsSmooth π := by
  obtain ⟨_, _, _, -, -, e, hs⟩ := h
  exact hs.isSmooth (isSmooth_parInd _ _)

theorem HasSupport.isCusp (h : HasSupport π s) {y : IrrGL k} (hy : y ∈ s) : y.IsCusp := by
  obtain ⟨_, x, rfl, hc⟩ := h
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨(hc.2.1 a).1, (hc.2.1 a).2.2⟩

theorem HasSupport.sum_fst (h : HasSupport π s) : (s.map Sigma.fst).sum = Fintype.card n := by
  obtain ⟨_, x, rfl, -, -, e, -⟩ := h
  rw [Multiset.map_map, ← Fintype.card_congr e, Fintype.card_sigma]
  simp [Finset.sum_eq_multiset_sum]

theorem HasSupport.of_equiv (h : HasSupport π s) {σ : Representation ℂ (GL n k) W} (φ : π.Equiv σ) : HasSupport σ s := by
  obtain ⟨h', x, hx, hi, hc, e, hs⟩ := h
  exact ⟨h', x, hx, isIrreducible_of_equiv φ hi, hc, e,
    (IsSubquotient.of_surjective φ.toIntertwiningMap (EquivLike.surjective φ)).trans hs⟩

theorem hasSupport_of_isCuspSupport {h : ℕ} {d : Fin h → ℕ} {X : Fin h → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)} (H : IsCuspSupport π d σ) :
    HasSupport π (Finset.univ.val.map fun a => IrrGL.of (σ a) (H.2.1 a).2.2.1 (H.2.1 a).2.1) := by
  obtain ⟨e, hs⟩ := H.2.2
  let x : Fin h → IrrGL k := fun a => IrrGL.of (σ a) (H.2.1 a).2.2.1 (H.2.1 a).2.1
  have φ : ∀ a, (σ a).Equiv (x a).rep := fun a => IrrGL.equivOf (σ a) (H.2.1 a).2.2.1 (H.2.1 a).2.1
  refine ⟨h, x, rfl, H.1, fun a => ⟨(H.2.1 a).1, isIrreducible_of_equiv (φ a) (H.2.1 a).2.1,
    isCuspidal_of_equiv (φ a) (H.2.1 a).2.2⟩, e, hs.trans ?_⟩
  exact IsSubquotient.of_surjective (multiProdEquiv e φ).symm.toIntertwiningMap (EquivLike.surjective (multiProdEquiv e φ).symm)

theorem hasSupport_of_isSubquotient {h N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible)
    {x : Fin h → IrrGL k} (hc : ∀ a, (x a).IsCusp) {hd : ∑ a, (x a).1 = N} (hs : IsSubquotient π (prodIrr x hd)) :
    HasSupport π (Finset.univ.val.map x) := ⟨h, x, rfl, hi, fun a => ⟨(hc a).1, (x a).2.rep.irr, (hc a).2⟩, stdBlocks _ hd, hs⟩

theorem hasSupport_self {x : IrrGL k} (hx : x.IsCusp) : HasSupport x.rep {x} := by
  have hd : ∑ _ : Fin 1, x.1 = x.1 := by simp
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one x hd
  exact ⟨1, fun _ => x, by simp, x.2.rep.irr, fun _ => ⟨hx.1, x.2.rep.irr, hx.2⟩, stdBlocks _ hd,
    IsSubquotient.of_injective φ.toIntertwiningMap (EquivLike.injective φ)⟩

end Support

end GlobalTheory.LocGL

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def first (Δ : Segment k) : IrrGL k := ⟨Δ.d, Δ.start⟩

theorem isCusp_first (Δ : Segment k) : Δ.first.IsCusp := by
  obtain ⟨σ, hσ, hc⟩ := Δ.cusp
  exact ⟨Δ.d_pos, isCuspidal_of_equiv (cl_eq_iff_rep.1 hσ).some hc⟩

def ofFirst (ρ : IrrGL k) (hρ : ρ.IsCusp) (l : ℕ) (hl : 0 < l) : Segment k :=
  ⟨ρ.1, hρ.1, ρ.2, ⟨ρ.2.rep, ρ.2.cl_rep, hρ.2⟩, l, hl⟩

@[simp] theorem first_ofFirst (ρ : IrrGL k) (hρ : ρ.IsCusp) (l : ℕ) (hl : 0 < l) : (ofFirst ρ hρ l hl).first = ρ := rfl

@[simp] theorem len_ofFirst (ρ : IrrGL k) (hρ : ρ.IsCusp) (l : ℕ) (hl : 0 < l) : (ofFirst ρ hρ l hl).len = l := rfl

theorem ext_first {Δ Δ' : Segment k} (h : Δ.first = Δ'.first) (h' : Δ.len = Δ'.len) : Δ = Δ' := by
  obtain ⟨d, hd, s, hs, l, hl⟩ := Δ
  obtain ⟨d', hd', s', hs', l', hl'⟩ := Δ'
  simp only [Segment.first, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  obtain rfl := eq_of_heq h2
  dsimp only at h'
  subst h'
  rfl

def single (ρ : IrrGL k) (hρ : ρ.IsCusp) : Segment k := ofFirst ρ hρ 1 one_pos

def icc (ρ : IrrGL k) (hρ : ρ.IsCusp) (c d : ℤ) (h : c ≤ d) : Segment k :=
  ofFirst (ρ.nu c) (hρ.nu c) (d - c + 1).toNat (by omega)

def term (Δ : Segment k) (a : Fin Δ.len) : IrrGL k := Δ.first.nu (a : ℕ)

def carrier (Δ : Segment k) : Set (IrrGL k) := Set.range Δ.term

def ms (Δ : Segment k) : Multiset (IrrGL k) := Finset.univ.val.map Δ.term

def deg (Δ : Segment k) : ℕ := Δ.len * Δ.d

def tw (Δ : Segment k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Segment k :=
  ofFirst (Δ.first.tw χ hχ) (Δ.isCusp_first.tw χ hχ) Δ.len Δ.len_pos

def nu (Δ : Segment k) (s : ℂ) : Segment k := Δ.tw (absPow k s) (isSmoothChar_absPow s)

def Linked (Δ Δ' : Segment k) : Prop :=
  (∃ Γ : Segment k, Γ.carrier = Δ.carrier ∪ Δ'.carrier) ∧ ¬ Δ.carrier ⊆ Δ'.carrier ∧ ¬ Δ'.carrier ⊆ Δ.carrier

def Precedes (Δ Δ' : Segment k) : Prop := Linked Δ Δ' ∧ ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j

theorem isCusp_term (Δ : Segment k) (a : Fin Δ.len) : (Δ.term a).IsCusp := Δ.isCusp_first.nu _

theorem sum_term_fst (Δ : Segment k) : ∑ a, (Δ.term a).1 = Δ.deg := by
  show ∑ _a : Fin Δ.len, Δ.d = Δ.len * Δ.d
  simp

theorem mem_carrier {Δ : Segment k} {x : IrrGL k} : x ∈ Δ.carrier ↔ ∃ a : ℕ, a < Δ.len ∧ Δ.first.nu a = x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem mem_ms {Δ : Segment k} {x : IrrGL k} : x ∈ Δ.ms ↔ x ∈ Δ.carrier := by
  simp [Segment.ms, Segment.carrier]

@[simp] theorem card_ms (Δ : Segment k) : Δ.ms.card = Δ.len := by
  simp [Segment.ms]

theorem mem_icc {ρ : IrrGL k} {hρ : ρ.IsCusp} {c d : ℤ} {h : c ≤ d} {x : IrrGL k} :
    x ∈ (icc ρ hρ c d h).carrier ↔ ∃ a : ℤ, c ≤ a ∧ a ≤ d ∧ ρ.nu a = x := by
  rw [mem_carrier]
  show (∃ a : ℕ, a < (d - c + 1).toNat ∧ (ρ.nu c).nu a = x) ↔ _
  simp only [IrrGL.nu_nu]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Int.lt_toNat] at ha
    refine ⟨c + a, by omega, by omega, ?_⟩
    congr 1
    push_cast
    ring
  · rintro ⟨a, h1, h2, rfl⟩
    have h3 : ((a - c).toNat : ℤ) = a - c := Int.toNat_of_nonneg (by omega)
    refine ⟨(a - c).toNat, by omega, ?_⟩
    congr 1
    have h4 : (((a - c).toNat : ℕ) : ℂ) = (a : ℂ) - c := by exact_mod_cast h3
    rw [h4]
    ring

@[simp] theorem carrier_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : (single ρ hρ).carrier = {ρ} := by
  show Set.range (fun a : Fin 1 => ρ.nu ((a : ℕ) : ℂ)) = {ρ}
  rw [Set.range_unique]
  simp

@[simp] theorem ms_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : (single ρ hρ).ms = {ρ} := by
  show Finset.univ.val.map (fun a : Fin 1 => ρ.nu ((a : ℕ) : ℂ)) = {ρ}
  simp

theorem Linked.symm {Δ Δ' : Segment k} (h : Linked Δ Δ') : Linked Δ' Δ := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  exact ⟨⟨Γ, hΓ.trans (Set.union_comm _ _)⟩, h2, h1⟩

theorem not_linked_self (Δ : Segment k) : ¬ Linked Δ Δ := fun h => h.2.1 (Set.Subset.refl _)

theorem inert_of_mem {Δ : Segment k} {x : IrrGL k} (h : x ∈ Δ.carrier) : IrrGL.Inert Δ.first x := by
  obtain ⟨a, -, rfl⟩ := mem_carrier.1 h
  exact IrrGL.inert_nu _ _
private theorem first_mem_carrier' (Δ : Segment k) : Δ.first ∈ Δ.carrier :=
  ⟨⟨0, Δ.len_pos⟩, by simp [Segment.term]⟩

theorem Linked.inert {Δ Δ' : Segment k} (h : Linked Δ Δ') : IrrGL.Inert Δ.first Δ'.first := by
  obtain ⟨⟨Γ, hΓ⟩, -, -⟩ := h
  have h1 : Δ.first ∈ Γ.carrier := hΓ ▸ Or.inl (first_mem_carrier' Δ)
  have h2 : Δ'.first ∈ Γ.carrier := hΓ ▸ Or.inr (first_mem_carrier' Δ')
  exact IrrGL.inert_equivalence.trans (IrrGL.inert_equivalence.symm (inert_of_mem h1)) (inert_of_mem h2)

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N h : ℕ}

def msupp (𝔪 : Multiset (Segment k)) : Multiset (IrrGL k) := 𝔪.bind Segment.ms

def Unlinked (𝔪 𝔫 : Multiset (Segment k)) : Prop := ∀ Δ ∈ 𝔪, ∀ Δ' ∈ 𝔫, ¬ Δ.Linked Δ'

def TotallyUnlinked (𝔪 : Multiset (Segment k)) : Prop := Unlinked 𝔪 𝔪

def IsOrderedForm (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)) : Prop :=
  Finset.univ.val.map Δ = 𝔪 ∧ ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)

def IsZSeg (Δ : Segment k) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ hd : ∑ a, (Δ.term a).1 = N, IsSocle π (prodIrr Δ.term hd)

def IsLSeg (Δ : Segment k) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ hd : ∑ a, (Δ.term a).1 = N, IsCosocle π (prodIrr Δ.term hd)

def ZFactors (𝔪 : Multiset (Segment k)) (x : Fin h → IrrGL k) : Prop :=
  ∃ Δ : Fin h → Segment k, IsOrderedForm Δ 𝔪 ∧ ∀ i, IsZSeg (Δ i) (x i).rep

def LFactors (𝔪 : Multiset (Segment k)) (x : Fin h → IrrGL k) : Prop :=
  ∃ Δ : Fin h → Segment k, IsOrderedForm Δ 𝔪 ∧ ∀ i, IsLSeg (Δ i) (x i).rep

def IsZ (𝔪 : Multiset (Segment k)) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), ZFactors 𝔪 x ∧ IsSocle π (prodIrr x hd)

def IsL (𝔪 : Multiset (Segment k)) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ IsCosocle π (prodIrr x hd)

def spehFactor (x : IrrGL k) (d : ℕ) (i : Fin d) : IrrGL k := x.nu (((d : ℂ) - 1) / 2 - (i : ℕ))

def IsSpeh (x : IrrGL k) (d : ℕ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ hd : ∑ a, (spehFactor x d a).1 = N, IsCosocle π (prodIrr (spehFactor x d) hd)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem unipB_mul_apply (u v : unipB k (Fin N)) {i j : Fin N} (hij : (j : ℕ) = i + 1) :
    ((u * v : unipB k (Fin N)) : GL (Fin N) k).val i j = (u : GL (Fin N) k).val i j + (v : GL (Fin N) k).val i j := by
  have hu := mem_unipRad.1 u.2
  have hv := mem_unipRad.1 v.2
  have lo : ∀ g : GL (Fin N) k, g ∈ parab k (points (Fin N)) → ∀ p q : Fin N, q < p →
      (g : Matrix (Fin N) (Fin N) k) p q = 0 :=
    fun g hg p q hpq => mem_parab.1 hg p q (by simpa [blk, points] using hpq)
  have di : ∀ g : GL (Fin N) k, (∀ (a : Fin N) (i j : Unit), (g : Matrix (Fin N) (Fin N) k) (points (Fin N) ⟨a, i⟩)
      (points (Fin N) ⟨a, j⟩) = (1 : Matrix Unit Unit k) i j) → ∀ p, (g : Matrix (Fin N) (Fin N) k) p p = 1 :=
    fun g hg p => by simpa using hg p () ()
  have hij' : i ≠ j := fun h => by rw [h] at hij; omega
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add i j hij' fun l hl => ?_]
  · rw [di _ hu.2 i, di _ hv.2 j]
    ring
  · by_cases h1 : l < i
    · rw [lo _ hu.1 i l h1, zero_mul]
    · have h2 : (j : ℕ) < l := by
        have := Fin.val_ne_of_ne hl.1
        have := Fin.val_ne_of_ne hl.2
        rw [Fin.lt_def] at h1
        omega
      rw [lo _ hv.1 l j (Fin.lt_def.2 h2), mul_zero]

def whitChar (ψ : AddChar k Circle) (N : ℕ) : unipB k (Fin N) →* ℂˣ where
  toFun u := Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin N) k).val p.1 p.2))
  map_one' := by
    rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
    intro p hp
    exact Matrix.one_apply_ne fun e => by have := (Finset.mem_filter.1 hp).2; rw [e] at this; omega
  map_mul' u v := by
    rw [← map_mul, ← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
    exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun p hp => unipB_mul_apply u v (Finset.mem_filter.1 hp).2))

def IsGenericFor (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  Nontrivial (TwJacquet π (unipB k (Fin N)) (whitChar ψ N))

def IsGeneric (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1 ∧ IsGenericFor ψ π

@[simp] theorem msupp_add (𝔪 𝔫 : Multiset (Segment k)) : msupp (𝔪 + 𝔫) = msupp 𝔪 + msupp 𝔫 := by
  simp [msupp]

@[simp] theorem msupp_singleton (Δ : Segment k) : msupp {Δ} = Δ.ms := by
  simp [msupp]

section Equiv

variable {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W} {Δ : Segment k}
  {𝔪 : Multiset (Segment k)}

theorem IsZSeg.of_equiv (h : IsZSeg Δ π) (φ : π.Equiv σ) : IsZSeg Δ σ := by
  obtain ⟨hd, hs⟩ := h
  exact ⟨hd, hs.of_equiv φ (Representation.Equiv.refl _)⟩

theorem IsLSeg.of_equiv (h : IsLSeg Δ π) (φ : π.Equiv σ) : IsLSeg Δ σ := by
  obtain ⟨hd, hs⟩ := h
  exact ⟨hd, hs.of_equiv φ (Representation.Equiv.refl _)⟩

theorem IsZ.of_equiv (h : IsZ 𝔪 π) (φ : π.Equiv σ) : IsZ 𝔪 σ := by
  obtain ⟨h, x, hd, hz, hs⟩ := h
  exact ⟨h, x, hd, hz, hs.of_equiv φ (Representation.Equiv.refl _)⟩

theorem IsL.of_equiv (h : IsL 𝔪 π) (φ : π.Equiv σ) : IsL 𝔪 σ := by
  obtain ⟨h, x, hd, hz, hs⟩ := h
  exact ⟨h, x, hd, hz, hs.of_equiv φ (Representation.Equiv.refl _)⟩

theorem IsZSeg.unique (h : IsZSeg Δ π) (h' : IsZSeg Δ σ) : Nonempty (σ.Equiv π) := by
  obtain ⟨hd, hs⟩ := h
  obtain ⟨hd', hs'⟩ := h'
  exact IsSocle.unique hs hs'

theorem IsLSeg.unique (h : IsLSeg Δ π) (h' : IsLSeg Δ σ) : Nonempty (σ.Equiv π) := by
  obtain ⟨hd, hs⟩ := h
  obtain ⟨hd', hs'⟩ := h'
  exact IsCosocle.unique hs hs'

theorem IsZSeg.hasSupport (h : IsZSeg Δ π) : HasSupport π Δ.ms := by
  obtain ⟨hd, hs⟩ := h
  exact ⟨Δ.len, Δ.term, rfl, hs.1, fun a => ⟨(Δ.isCusp_term a).1, (Δ.term a).2.rep.irr, (Δ.isCusp_term a).2⟩,
    stdBlocks _ hd, hs.isSubquotient⟩

theorem IsLSeg.hasSupport (h : IsLSeg Δ π) : HasSupport π Δ.ms := by
  obtain ⟨hd, hs⟩ := h
  exact ⟨Δ.len, Δ.term, rfl, hs.1, fun a => ⟨(Δ.isCusp_term a).1, (Δ.term a).2.rep.irr, (Δ.isCusp_term a).2⟩,
    stdBlocks _ hd, hs.isSubquotient⟩

theorem IsZSeg.deg_eq (h : IsZSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  exact Δ.sum_term_fst.symm.trans hd

theorem IsLSeg.deg_eq (h : IsLSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  exact Δ.sum_term_fst.symm.trans hd

theorem IsZ.irr_smooth (h : IsZ 𝔪 π) : π.IsIrreducible ∧ IsSmooth π := by
  obtain ⟨h, x, hd, -, hs⟩ := h
  exact ⟨hs.1, hs.isSubquotient.isSmooth (isSmooth_prodIrr x hd)⟩

theorem IsL.irr_smooth (h : IsL 𝔪 π) : π.IsIrreducible ∧ IsSmooth π := by
  obtain ⟨h, x, hd, -, hs⟩ := h
  exact ⟨hs.1, hs.isSubquotient.isSmooth (isSmooth_prodIrr x hd)⟩

theorem isOrderedForm_one (Δ : Segment k) :
    IsOrderedForm (fun _ : Fin 1 => Δ) {Δ} := ⟨by simp, fun i j hij => absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl j)⟩

theorem IsZSeg.isZ (h : IsZSeg Δ π) : IsZ {Δ} π := by
  obtain ⟨hd, hs⟩ := h
  have hsm : IsSmooth π := hs.isSubquotient.isSmooth (isSmooth_prodIrr _ hd)
  let y : IrrGL k := IrrGL.of π hsm hs.1
  have hd1 : ∑ _a : Fin 1, y.1 = y.1 := by simp
  obtain ⟨e⟩ := nonempty_equiv_prodIrr_one y hd1
  have e' : π.Equiv (prodIrr (fun _ : Fin 1 => y) hd1) := (IrrGL.equivOf π hsm hs.1).trans e
  have hS : IsSocle π (prodIrr (fun _ : Fin 1 => y) hd1) := (isSocle_self hs.1).of_equiv (Representation.Equiv.refl π) e'
  have hZ : IsZSeg Δ y.rep := ⟨hd, hs.of_equiv (IrrGL.equivOf π hsm hs.1) (Representation.Equiv.refl _)⟩
  exact ⟨1, fun _ => y, hd1, ⟨fun _ => Δ, isOrderedForm_one Δ, fun _ => hZ⟩, hS⟩

theorem IsLSeg.isL (h : IsLSeg Δ π) : IsL {Δ} π := by
  obtain ⟨hd, hs⟩ := h
  have hsm : IsSmooth π := hs.isSubquotient.isSmooth (isSmooth_prodIrr _ hd)
  let y : IrrGL k := IrrGL.of π hsm hs.1
  have hd1 : ∑ _a : Fin 1, y.1 = y.1 := by simp
  obtain ⟨e⟩ := nonempty_equiv_prodIrr_one y hd1
  have e' : π.Equiv (prodIrr (fun _ : Fin 1 => y) hd1) := (IrrGL.equivOf π hsm hs.1).trans e
  have hS : IsCosocle π (prodIrr (fun _ : Fin 1 => y) hd1) := (isCosocle_self hs.1).of_equiv (Representation.Equiv.refl π) e'
  have hZ : IsLSeg Δ y.rep := ⟨hd, hs.of_equiv (IrrGL.equivOf π hsm hs.1) (Representation.Equiv.refl _)⟩
  exact ⟨1, fun _ => y, hd1, ⟨fun _ => Δ, isOrderedForm_one Δ, fun _ => hZ⟩, hS⟩

end Equiv

def segProdEquiv (Δ : Segment k) (hd : ∑ a, (Δ.term a).1 = N) :
    (multiProd (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (segTerm Δ.start.rep.ρ Δ.len)).Equiv (prodIrr Δ.term hd) :=
  multiProdEquiv _ fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)

theorem IsZSeg.cl_eq {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) {Δ : Segment k}
    {π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)} (h : IsZSeg Δ π.ρ) : π.cl = Z Δ := by
  obtain ⟨hd, hs⟩ := h
  obtain ⟨f, hf, -⟩ := hs.2
  refine ((hZ Δ Δ.start.rep (IrrCl.cl_rep _) (stdBlocks (fun _ => Δ.d) hd) π).1).2
    ⟨(segProdEquiv Δ hd).symm.toIntertwiningMap.comp f, fun a b hab => hf ?_⟩
  exact EquivLike.injective (segProdEquiv Δ hd).symm hab
private theorem nonempty_equiv_prodIrr_fin_one (x : Fin 1 → IrrGL k) (y : IrrGL k) (hx : x 0 = y)
    (hd : ∑ a, (x a).1 = y.1) : Nonempty (y.rep.Equiv (prodIrr x hd)) := by
  obtain rfl : x = fun _ => y := funext fun a => by rw [Subsingleton.elim a 0, hx]
  exact nonempty_equiv_prodIrr_one y hd

theorem single_spec {ρ : IrrGL k} (hρ : ρ.IsCusp) :
    IsZSeg (.single ρ hρ) ρ.rep ∧ IsLSeg (.single ρ hρ) ρ.rep ∧ IsZ {.single ρ hρ} ρ.rep ∧ IsL {.single ρ hρ} ρ.rep := by
  have h0 : (Segment.single ρ hρ).term (0 : Fin 1) = ρ := by
    show ρ.nu ((((0 : Fin 1) : ℕ)) : ℂ) = ρ
    simp
  have hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1 := by
    show ∑ _a : Fin 1, ρ.1 = ρ.1
    simp
  obtain ⟨e⟩ := nonempty_equiv_prodIrr_fin_one (Segment.single ρ hρ).term ρ h0 hd
  have hZ : IsZSeg (.single ρ hρ) ρ.rep := ⟨hd, (isSocle_self ρ.2.rep.irr).of_equiv (.refl _) e⟩
  have hL : IsLSeg (.single ρ hρ) ρ.rep := ⟨hd, (isCosocle_self ρ.2.rep.irr).of_equiv (.refl _) e⟩
  exact ⟨hZ, hL, hZ.isZ, hL.isL⟩
private theorem rep_apply_eq_det_smul_of_eq_ofChar {ψ : kˣ →* ℂˣ} (hψ : IsSmoothChar ψ) (y : IrrGL k) (hy : y = IrrGL.ofChar ψ hψ)
    (g : GL (Fin y.1) k) (w : y.2.rep.V) : y.rep g w = (ψ (GeneralLinearGroup.det g) : ℂ) • w := by
  subst hy
  obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep (IrrRep.det (Fin 1) ψ hψ)
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g w
  have h2 : φ ((ψ (GeneralLinearGroup.det g) : ℂ) • w) = ((ψ (GeneralLinearGroup.det g) : ℂ)) • φ w := map_smul φ _ w
  apply EquivLike.injective φ
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (ofChar_apply (detChar (Fin 1) ψ) g (φ w)).trans rfl

theorem embeds_detRep_segment {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {l : ℕ} (hl : 0 < l)
    (hd : ∑ a, ((Segment.ofChar χ hχ l hl).term a).1 = N) :
    Embeds (detRep (Fin N) (χ * absPow k (((l : ℂ) - 1) / 2))) (prodIrr (Segment.ofChar χ hχ l hl).term hd) := by
  classical
  let x := (Segment.ofChar χ hχ l hl).term
  let e := stdBlocks (fun a => (x a).1) hd
  have hxa : ∀ a, x a = IrrGL.ofChar (χ * absPow k ((a : ℕ) : ℂ)) (hχ.mul (isSmoothChar_absPow _)) := fun a =>
    IrrGL.tw_ofChar χ _ hχ (isSmoothChar_absPow _)
  have hact : ∀ a (g : GL (Fin (x a).1) k) (w : (x a).2.rep.V),
      (x a).rep g w = ((χ * absPow k ((a : ℕ) : ℂ)) (GeneralLinearGroup.det g) : ℂ) • w := fun a g w =>
    rep_apply_eq_det_smul_of_eq_ofChar _ (x a) (hxa a) g w
  have hw : ∀ a, ∃ w : (x a).2.rep.V, w ≠ 0 := fun a => by
    haveI := nontrivial_of_irreducible (x a).2.rep.irr
    exact exists_ne 0
  choose w hw using hw
  have ht0ne : PiTensorProduct.tprod ℂ w ≠ 0 := by
    have hφ : ∀ a, ∃ φ : Module.Dual ℂ (x a).2.rep.V, φ (w a) ≠ 0 := fun a => by
      by_contra h
      push_neg at h
      exact hw a ((Module.forall_dual_apply_eq_zero_iff ℂ (w a)).1 h)
    choose φ hφ using hφ
    intro h0
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin (Segment.ofChar χ hχ l hl).len) ℂ).compLinearMap φ)) h0
    rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply] at h1
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hφ a) h1
  have hρ : ∀ M : Levi k (fun a => Fin (x a).1), piTensor (fun a => (x a).rep) M (PiTensorProduct.tprod ℂ w) =
      (∏ a : Fin (Segment.ofChar χ hχ l hl).len, ((χ * absPow k ((a : ℕ) : ℂ)) (GeneralLinearGroup.det (M a)) : ℂ)) • PiTensorProduct.tprod ℂ w := by
    intro M
    rw [piTensor_tprod]
    simp only [hact]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ _
  have hscal : ∀ p : parab k e,
      (((χ * absPow k (((l : ℂ) - 1) / 2)) (GeneralLinearGroup.det (p : GL (Fin N) k)) : ℂˣ) : ℂ) =
      (deltaHalf k (fun a => Fin (x a).1) (leviProj k e p) : ℂ) *
        ∏ a : Fin (Segment.ofChar χ hχ l hl).len, ((χ * absPow k ((a : ℕ) : ℂ)) (GeneralLinearGroup.det (leviProj k e p a)) : ℂ) := by
    intro p
    rw [det_parab k e p, map_prod, Units.coe_prod, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hme : ((modExp (fun b => Fin (x b).1) a : ℤ) : ℂ) / 2 + ((a : ℕ) : ℂ) = ((l : ℂ) - 1) / 2 := by
      rw [modExp_fin (fun b => Fin (x b).1) (fun i => Fintype.card_fin 1) a]
      have hlen : (((Segment.ofChar χ hχ l hl).len : ℕ) : ℂ) = (l : ℂ) := rfl
      push_cast
      rw [hlen]
      ring
    rw [← hme, absPow_add]
    simp only [MonoidHom.mul_apply, Units.val_mul]
    ring
  let σ' := (twist (piTensor fun a => (x a).rep) (deltaHalf k fun a => Fin (x a).1)).comp (leviProj k e)
  let F0 : indSpace (parab k e) σ' := ⟨fun g =>
      (((χ * absPow k (((l : ℂ) - 1) / 2)) (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ w,
    fun p g => by
      simp only [σ', MonoidHom.comp_apply, twist_apply, map_smul, hρ, smul_smul]
      rw [map_mul, map_mul, Units.val_mul, hscal p]
      congr 1
      ring⟩
  have hind : ∀ g : GL (Fin N) k, ind (parab k e) σ' g F0 =
      (((χ * absPow k (((l : ℂ) - 1) / 2)) (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • F0 := by
    intro g
    apply Subtype.ext
    funext y
    show (((χ * absPow k (((l : ℂ) - 1) / 2)) (GeneralLinearGroup.det (y * g)) : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ w =
      (((χ * absPow k (((l : ℂ) - 1) / 2)) (GeneralLinearGroup.det g) : ℂˣ) : ℂ) •
        ((((χ * absPow k (((l : ℂ) - 1) / 2)) (GeneralLinearGroup.det y) : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ w)
    rw [map_mul, map_mul, Units.val_mul, smul_smul, mul_comm]
  have hF0ne : F0 ≠ 0 := fun h => ht0ne (by
    have h1 := congrArg (fun f : indSpace (parab k e) σ' => f.1 1) h
    simpa [F0] using h1)
  have hsm : F0 ∈ smoothPart (ind (parab k e) σ') := by
    show IsOpen {g | ind (parab k e) σ' g F0 = F0}
    have hset : {g | ind (parab k e) σ' g F0 = F0} =
        ((detChar (Fin N) (χ * absPow k (((l : ℂ) - 1) / 2))).ker : Set (GL (Fin N) k)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, MonoidHom.mem_ker, hind, detChar_apply]
      constructor
      · intro h
        exact Units.val_eq_one.1 (smul_left_injective ℂ hF0ne (h.trans (one_smul ℂ F0).symm))
      · intro h
        rw [h, Units.val_one, one_smul]
    rw [hset]
    exact (hχ.mul (isSmoothChar_absPow _)).detChar
  let F0' : IndSp e (piTensor fun a => (x a).rep) := ⟨F0, hsm⟩
  let Φ : (detRep (Fin N) (χ * absPow k (((l : ℂ) - 1) / 2))).IntertwiningMap (prodIrr x hd) :=
    ⟨LinearMap.toSpanSingleton ℂ _ F0', fun g => LinearMap.ext fun z => by
      apply Subtype.ext
      change (detRep (Fin N) (χ * absPow k (((l : ℂ) - 1) / 2)) g z) • F0 = ind (parab k e) σ' g (z • F0)
      rw [map_smul, hind, smul_smul]
      congr 1
      simp only [detRep, ofChar_apply, detChar_apply]
      ring⟩
  refine ⟨Φ, fun z z' h => ?_⟩
  have h2 : z • F0 = z' • F0 := congrArg Subtype.val (show z • F0' = z' • F0' from h)
  exact smul_left_injective ℂ hF0ne h2

theorem IsZSeg.equiv_detRep {χ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} {l : ℕ} {hl : 0 < l}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsZSeg (Segment.ofChar χ hχ l hl) π) :
    Nonempty ((detRep (Fin N) (χ * absPow k (((l : ℂ) - 1) / 2))).Equiv π) := by
  obtain ⟨hd, hs⟩ := h
  exact hs.equiv_of_embeds (isIrreducible_ofChar _) (embeds_detRep_segment hχ hl hd)

theorem hasSupport_detRep {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {l : ℕ} (hl : 0 < l) :
    HasSupport (detRep (Fin l) (χ * absPow k (((l : ℂ) - 1) / 2))) (Segment.ofChar χ hχ l hl).ms := by
  have hd : ∑ a, ((Segment.ofChar χ hχ l hl).term a).1 = l := (Segment.sum_term_fst _).trans (mul_one l)
  obtain ⟨f, hf⟩ := embeds_detRep_segment hχ hl hd
  exact ⟨l, (Segment.ofChar χ hχ l hl).term, rfl, isIrreducible_ofChar _,
    fun a => ⟨((Segment.ofChar χ hχ l hl).isCusp_term a).1, (((Segment.ofChar χ hχ l hl).term a)).2.rep.irr,
      ((Segment.ofChar χ hχ l hl).isCusp_term a).2⟩, stdBlocks _ hd, IsSubquotient.of_injective f hf⟩

theorem single_precedes (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (Segment.single _ (IrrGL.isCusp_ofChar χ hχ)).Precedes (.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)) ∧
      ¬ (Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)).Precedes (.single _ (IrrGL.isCusp_ofChar χ hχ)) := by
  have hc := IrrGL.isCusp_ofChar χ hχ
  have hne : IrrGL.ofChar χ hχ ≠ (IrrGL.ofChar χ hχ).nu 1 := by
    intro h
    have h0 := (IrrGL.nu_ofChar_inj χ hχ (s := 0) (t := 1)).1 (by simpa using h)
    norm_num at h0
  refine ⟨⟨⟨⟨Segment.ofFirst (IrrGL.ofChar χ hχ) hc 2 (by norm_num), ?_⟩, ?_, ?_⟩, 1, one_pos, ?_⟩, ?_⟩
  · ext y
    rw [Segment.mem_carrier, Segment.carrier_single, Segment.carrier_single]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      interval_cases a
      · left
        simp
      · right
        simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_singleton]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_singleton]
    exact fun h => hne h.symm
  · show (IrrGL.ofChar χ hχ).nu 1 = (IrrGL.ofChar χ hχ).nu ((1 : ℕ) : ℂ)
    simp
  · rintro ⟨-, j, hj, h⟩
    change IrrGL.ofChar χ hχ = ((IrrGL.ofChar χ hχ).nu 1).nu ((j : ℕ) : ℂ) at h
    rw [IrrGL.nu_nu] at h
    have h0 := (IrrGL.nu_ofChar_inj χ hχ (s := 0) (t := 1 + j)).1 (by push_cast; simpa using h)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith

theorem isSpeh_one (x : IrrGL k) : IsSpeh x 1 x.rep := by
  have h0 : spehFactor x 1 (0 : Fin 1) = x := by simp [spehFactor]
  have hd : ∑ a : Fin 1, (spehFactor x 1 a).1 = x.1 := by simp [spehFactor]
  obtain ⟨e⟩ := nonempty_equiv_prodIrr_fin_one (spehFactor x 1) x h0 hd
  exact ⟨hd, (isCosocle_self x.2.rep.irr).of_equiv (.refl _) e⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isGenericFor_one (ψ : AddChar k Circle) (χ : kˣ →* ℂˣ) : IsGenericFor ψ (detRep (Fin 1) χ) := by
  have hu : ∀ u : unipB k (Fin 1), u = 1 := by
    intro u
    have hd := (mem_unipRad.1 u.2).2
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa using hd 0 () ()
  have hbot : twKer (detRep (Fin 1) χ) (unipB k (Fin 1)) (whitChar ψ 1) = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨u, v, rfl⟩
    rw [hu u]
    simp
  exact (Submodule.quotEquivOfEqBot _ hbot).toEquiv.nontrivial

end GlobalTheory.LocGL
