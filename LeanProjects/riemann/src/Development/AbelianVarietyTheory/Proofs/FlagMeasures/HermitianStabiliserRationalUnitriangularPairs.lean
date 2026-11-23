import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab

section Local
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]

theorem hfR_smul (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R) (s t : R) (x y : Fin n → R) :
    hf L Hm (s • x) (t • y) = s * L.cj t * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hfR_add (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R) (x y z : Fin n → R) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hfR_smulr (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R) (t : R) (x y : Fin n → R) :
    hf L Hm x (t • y) = L.cj t * hf L Hm x y := by
  have := hfR_smul L Hm 1 t x y
  rwa [one_smul, one_mul] at this

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem exists_place : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

def bcL (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (Fin n → E) →ₛₗ[(A.loc p).ιE] (Fin n → (A.loc p).Ep) where
  toFun := A.bc p
  map_add' x y := by funext i; simp [Places.bc]
  map_smul' c x := by funext i; simp [Places.bc]

theorem bcL_apply (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : Fin n → E) :
    bcL A p n x = A.bc p x := rfl

variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

def B (x y : G.V) : E := ∑ i, ∑ j, x i * G.Hm i j * sig (y j)

def sc (n : ℕ) : (A.loc p).Ep :=
  algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp))⁻¹ ^ (r - n))

def sci (n : ℕ) : (A.loc p).Ep :=
  algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - n))

theorem sc_mul_sci (n : ℕ) : sc G p n * sci G p n = 1 := by
  rw [sc, sci, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow, map_one]

theorem cj_sc (n : ℕ) : (A.L p).cj (sc G p n) = sc G p n := (A.L p).cj.commutes _

theorem cj_sci (n : ℕ) : (A.L p).cj (sci G p n) = sci G p n := (A.L p).cj.commutes _

theorem cj_ι (x : E) : (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x) := by
  rw [A.L_cj, (A.loc p).cj_ιE]

theorem f_scale (a : Fin (r + 1)) : (G.S p).f a = sc G p a • A.bc p (G.f a) := by
  rw [sc, ← G.f_eq p a, smul_smul, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow,
    map_one, one_smul]

theorem f'_scale (a : Fin (r + 1)) : (G.S p).f' a = sc G p a • A.bc p (G.f' a) := by
  rw [sc, ← G.f'_eq p a, smul_smul, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow,
    map_one, one_smul]

theorem herm_bc (x y : G.V) :
    hf (A.L p) (G.S p).Hm (A.bc p x) (A.bc p y) = (A.loc p).ιE (B G x y) := by
  rw [G.Hm_eq p]
  exact (RatExt.rational_extend A _ p).2.2.2.2.1 G.Hm x y

theorem Zh_scale (a b : Fin (r + 1)) :
    (G.S p).Zh a b = sc G p b * sc G p a * (A.loc p).ιE (G.Zh a b) := by
  simp only [Frames.Zh, Frames.h, Matrix.of_apply]
  rw [f_scale, f'_scale, hfR_smul, cj_sc, herm_bc]
  rfl

def locM (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep :=
  Matrix.of fun i j => sc G p j * sci G p i * (A.loc p).ιE (s i j)

theorem locM_unitri (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) :
    (∀ i j, j < i → locM G p s i j = 0) ∧ (∀ i, locM G p s i i = 1) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [locM, hs.1 i j h]
  · rw [locM, Matrix.of_apply, hs.2, map_one, mul_one, sc_mul_sci]

theorem mat_entry (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    (cT (A.L p) (locM G p s) * (G.S p).Zh * locM G p s') a b =
      sc G p a * sc G p b * (A.loc p).ιE (((s.map sig).transpose * G.Zh * s') a b) := by
  simp only [Matrix.mul_apply, cT, locM, Matrix.of_apply, Zh_scale, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, cj_sc, cj_sci, cj_ι, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  have h1 := sc_mul_sci G p i
  have h2 := sc_mul_sci G p l
  set X := (A.loc p).ιE (sig (s i a)) * (A.loc p).ιE (G.Zh i l) * (A.loc p).ιE (s' l b)
  linear_combination (sc G p a * sc G p b * X * sc G p l * sci G p l) * h1 + (sc G p a * sc G p b * X) * h2

end GlobalTheory.HL.RatStab

namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem mat_iff (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cT (A.L p) (locM G p s) * (G.S p).Zh * locM G p s' = (G.S p).Zh ↔
      (s.map sig).transpose * G.Zh * s' = G.Zh := by
  constructor
  · intro h
    ext a b
    have h1 := congrFun (congrFun h a) b
    rw [mat_entry, Zh_scale] at h1
    haveI : Nontrivial (A.loc p).Ep :=
      Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
    apply (A.loc p).ιE.injective
    have hu := sc_mul_sci G p a
    have hv := sc_mul_sci G p b
    set D := (A.loc p).ιE (((s.map sig).transpose * G.Zh * s') a b) - (A.loc p).ιE (G.Zh a b)
    linear_combination (sci G p a * sci G p b) * h1 - (D * sc G p b * sci G p b) * hu - D * hv
  · intro h
    ext a b
    rw [mat_entry, h, Zh_scale]
    ring

theorem bc_sum (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → G.V) (j : Fin (r + 1)) :
    A.bc p (∑ i, s i j • v i) = ∑ i, (A.loc p).ιE (s i j) • A.bc p (v i) := by
  simp only [← bcL_apply, map_sum, map_smulₛₗ]

theorem loc_of_glob (u : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (v : Fin (r + 1) → G.V)
    (hu : ∀ a, u a = sc G p a • A.bc p (v a)) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : G.GLV)
    (h' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep))
    (hE : A.Ext p h h') (hv : ∀ j, h (v j) = ∑ i, s i j • v i) (j : Fin (r + 1)) :
    h' (u j) = ∑ i, locM G p s i j • u i := by
  rw [hu j, map_smul, hE, hv j, bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hu i, smul_smul, smul_smul]
  congr 1
  simp only [locM, Matrix.of_apply]
  linear_combination (-(sc G p j * (A.loc p).ιE (s i j))) * sc_mul_sci G p i

theorem glob_of_loc (u : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (v : Fin (r + 1) → G.V)
    (hu : ∀ a, u a = sc G p a • A.bc p (v a)) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep))
    (hl : ∀ j, h' (u j) = ∑ i, locM G p s i j • u i) (j : Fin (r + 1)) :
    h' (A.bc p (v j)) = A.bc p (∑ i, s i j • v i) := by
  have hb : ∀ a, A.bc p (v a) = sci G p a • u a := fun a => by
    rw [hu a, smul_smul, mul_comm (sci G p a), sc_mul_sci, one_smul]
  rw [hb j, map_smul, hl j, bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb i, smul_smul, smul_smul]
  congr 1
  simp only [locM, Matrix.of_apply]
  linear_combination (sci G p i * (A.loc p).ιE (s i j)) * sc_mul_sci G p j

end GlobalTheory.HL.RatStab

namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

abbrev gg : Fin (r + 1) ⊕ Fin (r + 1) → G.V := Sum.elim G.f G.f'

abbrev idx : Fin (r + 1) ⊕ Fin (r + 1) → ℕ := Sum.elim (fun a => (a : ℕ)) (fun a => (a : ℕ))

def Phi : G.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) where
  toFun x j := B G x (gg G j)
  map_add' x y := by
    funext j
    simp only [B, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp only [B, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

def Wc : Submodule E G.V := LinearMap.ker (Phi G)

theorem gp_scale (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    Sum.elim (G.S p).f (G.S p).f' i = sc G p (idx i) • A.bc p (gg G i) := by
  rcases i with a | a
  · exact f_scale G p a
  · exact f'_scale G p a

theorem bc_gg (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    A.bc p (gg G i) = sci G p (idx i) • Sum.elim (G.S p).f (G.S p).f' i := by
  rw [gp_scale, smul_smul, mul_comm (sci G p _), sc_mul_sci, one_smul]

theorem decomp : LinearIndependent E (gg G) ∧ IsCompl (Submodule.span E (Set.range (gg G))) (Wc G) ∧
    ∀ x ∈ Wc G, A.bc p x ∈ (G.S p).W0 := by
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  have hME : (G.S p).ME = Submodule.span (A.loc p).Ep (Set.range (Sum.elim (G.S p).f (G.S p).f')) := by
    rw [Frames.ME, spanTo_top, spanTo_top, Set.Sum.elim_range, Submodule.span_union]
  have hinjbc : Function.Injective (A.bc (n := k + 2 * r + 1) p) := (RatExt.rational_extend A _ p).1

  have hind : LinearIndependent E (gg G) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 := congrArg (bcL A p _) hc
    simp only [map_sum, map_smulₛₗ, map_zero, bcL_apply, bc_gg, smul_smul] at h1
    have h2 := Fintype.linearIndependent_iff.1 hli _ h1 i
    apply (A.loc p).ιE.injective
    rw [map_zero]
    linear_combination sc G p (idx i) * h2 - (A.loc p).ιE (c i) * sc_mul_sci G p (idx i)

  have hW : ∀ x ∈ Wc G, A.bc p x ∈ (G.S p).W0 := by
    intro x hx y hy
    rw [hME] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have h0 : B G x (gg G i) = 0 := congrFun (LinearMap.mem_ker.1 hx) i
      rw [gp_scale, hfR_smulr, herm_bc, h0, map_zero, mul_zero]
    | zero => simp [hf]
    | add a b _ _ ha hb => rw [hfR_add, ha, hb, add_zero]
    | smul c a _ ha => rw [hfR_smulr, ha, mul_zero]

  have hM : ∀ m ∈ Submodule.span E (Set.range (gg G)), A.bc p m ∈ (G.S p).ME := by
    intro m hm
    have : Submodule.span E (Set.range (gg G)) ≤ Submodule.comap (bcL A p _) (G.S p).ME := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show A.bc p (gg G i) ∈ (G.S p).ME
      rw [bc_gg, hME]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact this hm
  have hdis : ∀ m ∈ Submodule.span E (Set.range (gg G)), m ∈ Wc G → m = 0 := by
    intro m hm hw
    apply hinjbc
    have h0 : A.bc p m = 0 := Submodule.disjoint_def.1 hco.disjoint _ (hM m hm) (hW m hw)
    rw [h0]
    funext i
    simp [Places.bc]
  refine ⟨hind, ⟨Submodule.disjoint_def.2 hdis, codisjoint_iff.2 ?_⟩, hW⟩

  set M := Submodule.span E (Set.range (gg G))
  have hinj : Function.Injective ((Phi G).comp M.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    have := hdis m m.2 (LinearMap.mem_ker.2 hm)
    exact (Submodule.mem_bot E).2 (Subtype.ext this)
  have hrk : Module.finrank E M = Module.finrank E (Fin (r + 1) ⊕ Fin (r + 1) → E) := by
    rw [finrank_span_eq_card hind, Module.finrank_fintype_fun_eq_card]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).1 hinj
  rw [eq_top_iff]
  intro x _
  obtain ⟨m, hm⟩ := hsurj (Phi G x)
  refine Submodule.mem_sup.2 ⟨m, m.2, x - m, ?_, by abel⟩
  rw [Wc, LinearMap.mem_ker, map_sub]
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at hm
  rw [hm, sub_self]

end GlobalTheory.HL.RatStab

namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab

theorem stab_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → ((s.map sig).transpose * G.Zh * s' = G.Zh ↔ ∃ h ∈ G.St, (∀ j, h (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, h (G.f' j) = ∑ i, s' i j • G.f' i) := by
  intro F E _ _ _ _ _ sig A r k G s s' hs hs'
  constructor
  · intro hz
    have hloc : ∀ p, ∃ h' ∈ (G.S p).St, (∀ j, h' ((G.S p).f j) = ∑ i, locM G p s i j • (G.S p).f i) ∧
        ∀ j, h' ((G.S p).f' j) = ∑ i, locM G p s' i j • (G.S p).f' i := fun p => by
      haveI := (A.loc p).lf
      haveI := (A.loc p).char0
      exact ((stab_eq (A.L p) r k (G.S p)).2 _ _ (locM_unitri G p s hs) (locM_unitri G p s' hs')).1
        ((mat_iff G p s s').2 hz)
    choose hp hpSt hpf hpf' using hloc
    obtain ⟨p0⟩ := exists_place (F := F)
    obtain ⟨hli, hco, -⟩ := decomp G p0
    let t : Fin (r + 1) ⊕ Fin (r + 1) → G.V :=
      Sum.elim (fun j => ∑ i, s i j • G.f i) (fun j => ∑ i, s' i j • G.f' i)
    let φ : G.V →ₗ[E] G.V :=
      LinearMap.ofIsCompl hco ((Module.Basis.span hli).constr E t) (Wc G).subtype
    have hφ1 : ∀ i, φ (gg G i) = t i := by
      intro i
      have h1 := LinearMap.ofIsCompl_apply_left hco (φ := (Module.Basis.span hli).constr E t)
        (ψ := (Wc G).subtype) (Module.Basis.span hli i)
      rw [Module.Basis.constr_basis, Module.Basis.span_apply] at h1
      exact h1
    have hφ2 : ∀ w ∈ Wc G, φ w = w := fun w hw =>
      LinearMap.ofIsCompl_apply_right hco (φ := (Module.Basis.span hli).constr E t)
        (ψ := (Wc G).subtype) ⟨w, hw⟩
    have hspan : Submodule.span E (Set.range (gg G) ∪ (Wc G : Set G.V)) = ⊤ := by
      rw [Submodule.span_union, Submodule.span_eq, hco.sup_eq_top]
    have hExt : ∀ p x, hp p (A.bc p x) = A.bc p (φ x) := by
      intro p
      haveI := (A.loc p).lf
      haveI := (A.loc p).char0
      have heq := LinearMap.ext_on (s := Set.range (gg G) ∪ (Wc G : Set G.V))
        (f := (hp p).toLinearMap.comp (bcL A p _)) (g := (bcL A p _).comp φ) hspan (by
          rintro x (⟨i, rfl⟩ | hx)
          · show hp p (A.bc p (gg G i)) = A.bc p (φ (gg G i))
            rw [hφ1]
            rcases i with j | j
            · exact glob_of_loc G p (G.S p).f G.f (f_scale G p) s (hp p) (hpf p) j
            · exact glob_of_loc G p (G.S p).f' G.f' (f'_scale G p) s' (hp p) (hpf' p) j
          · show hp p (A.bc p x) = A.bc p (φ x)
            rw [hφ2 x hx]
            exact (stab_eq (A.L p) r k (G.S p)).1 (hp p) (hpSt p) _ ((decomp G p).2.2 x hx))
      exact fun x => LinearMap.congr_fun heq x
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 := hExt p0 x
      rw [hx] at h1
      have h2 : A.bc p0 (0 : G.V) = 0 := by funext i; simp [Places.bc]
      rw [h2, LinearEquiv.map_eq_zero_iff] at h1
      exact (RatExt.rational_extend A _ p0).1 (h1.trans h2.symm)
    let h : G.GLV := LinearEquiv.ofBijective φ ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
    exact ⟨h, fun p => ⟨hp p, hpSt p, hExt p⟩, fun j => hφ1 (Sum.inl j), fun j => hφ1 (Sum.inr j)⟩
  · rintro ⟨h, hh, h1, h2⟩
    obtain ⟨p⟩ := exists_place (F := F)
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    have hh0 : ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p h g' := hh
    obtain ⟨h', hh', hE⟩ := hh0 p
    rw [← mat_iff G p]
    exact ((stab_eq (A.L p) r k (G.S p)).2 _ _ (locM_unitri G p s hs) (locM_unitri G p s' hs')).2
      ⟨h', hh', loc_of_glob G p (G.S p).f G.f (f_scale G p) s h h' hE h1,
        loc_of_glob G p (G.S p).f' G.f' (f'_scale G p) s' h h' hE h2⟩

end GlobalTheory.HL.RatStab
