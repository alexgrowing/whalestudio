import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.PsGen

open GlobalTheory.PRep GlobalTheory.JHMult

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem equiv_of_sub {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ)
    [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf y
  rcases eq_bot_or_eq_top S with rfl | rfl
  · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
  let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
  have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
  refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
  rcases eq_bot_or_eq_top F.ker with h | h
  · have : x ∈ F.ker := hx
    rw [h] at this
    exact this
  · have : v.1 ∈ F.ker := by rw [h]; trivial
    exact absurd this hy

private theorem equiv_of_between {U : Type} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ G U}
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient τ σ) (h' : IsSubquotient σ ρ)
    (hτ : τ.IsIrreducible) (hρ : ρ.IsIrreducible) : Nonempty (τ.Equiv σ) := by
  obtain ⟨t⟩ := (h.trans h').nonempty_equiv hτ hρ
  have hn := nontrivial_of_irreducible hτ
  haveI : Nontrivial W := by
    obtain ⟨S, f, hf⟩ := h
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  obtain ⟨r⟩ := equiv_of_sub h' hρ
  exact ⟨t.symm.trans r⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem irr_of_cls {π : Representation ℂ G V} (hs : IsSmooth π) (hf : HasFiniteLength π) (σ : IrrRep G)
    (h : GlobalTheory.SmGL.cls π hf = Finsupp.single σ.cl 1) : π.IsIrreducible := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hf
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have h1 : jhMult σ.ρ π = 1 := by
    obtain ⟨r, e1, e2⟩ := cls_apply_cl π hf σ
    rw [h, Finsupp.single_eq_same] at e2
    rw [e1]
    exact_mod_cast e2.symm
  have hq : ∀ S T : Subrepresentation π, T ⋖ S → jhMult σ.ρ (subQuot S T) = 1 := fun S T hT => by
    have hi := isIrreducible_subQuot hT
    have h2 : jhMult (subQuot S T) π ≠ 0 := by
      rw [← jhMult_congr_right _ (topEquiv π), jhMult_of_le hi (le_top : S ≤ ⊤), jhMult_of_le hi hT.le,
        jhMult_self hi]
      simp
    let τ : IrrRep G := ⟨_, subQuot S T, (jhMult_ne_zero_iff.1 h2).isSmooth hs, hi⟩
    obtain ⟨r, e1, e2⟩ := cls_apply_cl π hf τ
    have h3 : τ.cl = σ.cl := by
      by_contra hne
      rw [h, Finsupp.single_eq_of_ne hne] at e2
      have h4 : r = 0 := by exact_mod_cast e2.symm
      exact h2 (e1.trans (by rw [h4]; rfl))
    obtain ⟨e⟩ := IrrRep.cl_eq_iff.1 h3
    exact (jhMult_congr_right _ e).trans (jhMult_self σ.irr)
  have hnt : (⊥ : Subrepresentation π) ≠ ⊤ := fun e => by
    have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    rw [← jhMult_congr_right _ (topEquiv π), ← e, jhMult_of_subsingleton σ.irr] at h1
    exact zero_ne_one h1
  have : Nontrivial (Subrepresentation π) := ⟨_, _, hnt⟩
  refine ⟨fun S => ?_⟩
  by_contra hS
  rw [not_or] at hS
  obtain ⟨T, hT, hTS⟩ := exists_covBy_le_of_lt (bot_lt_iff_ne_bot.2 hS.1)
  obtain ⟨U, hSU, hU⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hS.2)
  rw [← jhMult_congr_right _ (topEquiv π), jhMult_of_le σ.irr hU.le, jhMult_of_le σ.irr (hTS.trans hSU),
    jhMult_of_le σ.irr hT.le, hq _ _ hT, hq _ _ hU] at h1
  have h5 : (2 : ℕ∞) ≤ 1 := by
    rw [← h1, ← one_add_one_eq_two]
    gcongr
    exact le_add_right le_add_self
  exact absurd h5 (by decide)

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isCusp_of_len {Δ : Segment k} (hl : Δ.len = 1) {y : IrrGL k} (h : IsLSeg Δ y.rep) : y.IsCusp := by
  have e : Segment.single Δ.first Δ.isCusp_first = Δ := Segment.ext_first rfl hl.symm
  have h1 := (single_spec Δ.isCusp_first).2.1
  rw [e] at h1
  obtain ⟨N, c⟩ := y
  obtain rfl : N = Δ.d := by
    have h2 : Δ.deg = N := h.deg_eq
    rw [← h2, Segment.deg, hl, one_mul]
  obtain ⟨φ⟩ := h1.unique h
  exact ⟨Δ.d_pos, isCuspidal_of_equiv φ.symm Δ.isCusp_first.2⟩

private theorem prin_sub {n : ℕ} (μ : Fin n → kˣ →* ℂˣ) (hμ : ∀ i, IsSmoothChar (μ i))
    (hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n) :
    IsSubquotient (prinSeries μ) (prodIrr (fun i => IrrGL.ofChar (μ i) (hμ i)) hd) := by
  obtain ⟨p⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
    (stdBlocks (fun _ : Fin n => 1) hd) _).1 (piTensor fun i => detRep (Fin 1) (μ i))
  let q := multiProdEquiv (stdBlocks (fun a => (IrrGL.ofChar (μ a) (hμ a)).1) hd) fun a =>
    equivRep (IrrRep.det (Fin 1) (μ a) (hμ a))
  exact ((GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n μ).trans
    (.of_injective p.toIntertwiningMap p.toLinearEquiv.injective)).trans
      (.of_injective q.toIntertwiningMap q.toLinearEquiv.injective)

private theorem irr_perm (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {n c c' : ℕ} (σ : IrrRep (GL (Fin n) k))
    (x : Fin c → IrrGL k) (y : Fin c' → IrrGL k) (hd : ∑ a, (x a).1 = n) (hd' : ∑ a, (y a).1 = n)
    (φ : σ.ρ.Equiv (prodIrr x hd)) (e : Finset.univ.val.map x = Finset.univ.val.map y) :
    (prodIrr y hd').IsIrreducible := by
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ x hd
  obtain ⟨hp', ep'⟩ := SupportRing.prodIrr_cls hΨ y hd'
  have e0 : ∏ a, SupportRing.bas Ψ (x a) = ∏ a, SupportRing.bas Ψ (y a) :=
    (SupportRing.pc_map x).symm.trans ((congrArg (SupportRing.pc Ψ) e).trans (SupportRing.pc_map y))
  have e1 : clsGL (prodIrr y hd') hp' = clsGL σ.ρ σ.hasFiniteLength :=
    (Ψ.injective (ep'.trans (e0.symm.trans ep.symm))).trans (clsGL_congr φ σ.hasFiniteLength hp).symm
  refine irr_of_cls (isSmooth_prodIrr y hd') hp' σ (Eq.trans ?_ (cls_irr σ σ.hasFiniteLength))
  exact Finsupp.ext fun z => (clsGL_apply _ hp' z).symm.trans
    ((DFunLike.congr_fun e1 _).trans (clsGL_apply _ σ.hasFiniteLength z))

private theorem equiv_prin [CharZero k] (H : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) {n c : ℕ} (σ : IrrRep (GL (Fin n) k))
    (x : Fin c → IrrGL k) (hx : ∀ a, (x a).IsCusp) (hd : ∑ a, (x a).1 = n) (φ : σ.ρ.Equiv (prodIrr x hd))
    (μ : Fin n → kˣ →* ℂˣ) (hμ : ∀ i, IsSmoothChar (μ i)) (hs : IsSubquotient σ.ρ (prinSeries μ)) :
    Nonempty (σ.ρ.Equiv (prinSeries μ)) := by
  let y : Fin n → IrrGL k := fun i => IrrGL.ofChar (μ i) (hμ i)
  have hd' : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
  have ψ := IrrGL.equivOf σ.ρ σ.smooth σ.irr
  have s1 : HasSupport σ.ρ (Finset.univ.val.map x) :=
    hasSupport_of_isSubquotient σ.irr hx (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have s2 : HasSupport σ.ρ (Finset.univ.val.map y) := hasSupport_of_isSubquotient_prinSeries k n μ hμ σ hs
  have e := SupportUnique.hasSupport_unique H.geo H.bz H.zel k _ _ _ (s1.of_equiv ψ) (s2.of_equiv ψ)
  have hi := irr_perm H.zel σ x y hd hd' φ e
  have h1 : IsSubquotient (prinSeries μ) (prodIrr y hd') := prin_sub μ hμ hd'
  exact equiv_of_between hs h1 σ.irr hi

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem mono_of_mem_sum_list {l : List (WD h)} (hl : (sumList l).mono0) {z : WD h} (hz : z ∈ l) : z.mono0 := by
  induction l with
  | nil => cases hz
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := (WD.monomial_sum_iff a (sumList l)).1 hl
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h1
    · exact ih h2 hz

private theorem le_one_of_mono0 {z : WD h} (hz : IsIrrWD z) (s : ℝ) {l : ℕ}
    (h0 : ((z.lpTw s).lpChar (WD.lpSp h l)).mono0) : l ≤ 1 := by
  obtain ⟨m, b, rfl, hb⟩ := hz
  by_contra hl
  rw [WD.lpTw_mk, WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, WDRep.sp_N] at h0
  haveI : Nontrivial (Fin m → ℂ) := nontrivial_of_irreducible hb
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
  have h1 := congrArg (fun t => TensorProduct.rid ℂ _
    (LinearMap.lTensor (Fin m → ℂ) (LinearMap.proj (⟨1, by omega⟩ : Fin l) : (Fin l → ℂ) →ₗ[ℂ] ℂ) t))
    (LinearMap.congr_fun h0 (v ⊗ₜ Pi.single ⟨0, by omega⟩ 1))
  apply hv
  simpa [shiftEnd_apply] using h1

end WD

end UpperTheory.V.Hi.PsGen

theorem UpperTheory.V.Hi.psGen :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, IsRec h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → IsSubquotient σ.ρ (PS ω) → (∃ b : WDRep h (Fin n → ℂ), WD.mk b = rc (algNorm σ) ∧ b.N = 0) → (∃ ψ : AddChar (w.adicCompletion L) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ σ.ρ) → Nonempty (σ.ρ.Equiv (PS ω)) := by
  rintro P L Ω _ _ _ _ _ n w A h a - rc ⟨a', ha', ε, -, H⟩ σ ω hω hs ⟨b, hb, hN⟩ ⟨ψ, hc, h1, hg⟩
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  obtain ⟨c, Δ, x, hd, hun, hL, ⟨φ⟩⟩ := P.loc.gen _ n _ σ.ρ σ.smooth σ.irred
    ⟨ψ, hc, h1, (GlobalTheory.Whittaker.isGeneric_iff_isGenericFor ψ σ.ρ).1 hg⟩
  have hm : (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).mono0 := by
    have h2 := (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN
    rwa [hb, algNorm, H.nu_eq, WD.monomial_twist_iff] at h2
  have hIsL : IsL ((List.ofFn Δ : List _) : Multiset _) σ.ρ :=
    ⟨c, x, hd, ⟨Δ, ⟨Fin.univ_val_map _, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩,
      (isCosocle_self σ.irred).of_equiv (.refl _) φ⟩
  rw [H.langlands _ _ (hIsL.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred))] at hm
  have hlen : ∀ i, (Δ i).len = 1 := fun i =>
    le_antisymm (PsGen.le_one_of_mono0 ((H.cusp _).1 (Δ i).isCusp_first) _
      (PsGen.mono_of_mem_sum_list hm (List.mem_map_of_mem (List.mem_ofFn.2 ⟨i, rfl⟩)))) (Δ i).len_pos
  exact PsGen.equiv_prin P.loc ⟨_, σ.ρ, σ.smooth, σ.irred⟩ x (fun i => PsGen.isCusp_of_len (hlen i) (hL i)) hd φ _
    (fun i => (hω i).mul (isSmoothChar_absPow _)) hs
