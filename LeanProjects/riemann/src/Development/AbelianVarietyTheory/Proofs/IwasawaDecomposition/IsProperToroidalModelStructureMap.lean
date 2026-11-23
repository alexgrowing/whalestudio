import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompNonemptyFiniteGenFrTrdeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open TopologicalSpace
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.SharedLaws

section Top

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

theorem exists_finite_generic {F : Set X} (hF : IsClosed F) :
    ∃ G : Set X, G.Finite ∧ G ⊆ F ∧ ∀ x ∈ F, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose η hη using fun t (ht : t ∈ S) => QuasiSober.sober (hi t ht) (hc t ht)
  haveI := hS.to_subtype
  refine ⟨Set.range fun t : S => η t.1 t.2, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t.1, t.2, (hη t.1 t.2).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hη t ht).specializes hx⟩

theorem finite_maximal {F : Set X} (hF : IsClosed F) :
    Finite {x : X // x ∈ F ∧ ∀ x' : X, x' ∈ F → x' ⤳ x → x' = x} := by
  obtain ⟨G, hG, hGF, h⟩ := exists_finite_generic hF
  refine (hG.subset (s := G) (t := {x | x ∈ F ∧ ∀ x' : X, x' ∈ F → x' ⤳ x → x' = x}) ?_).to_subtype
  rintro x ⟨hx, hm⟩
  obtain ⟨g, hg, hgx⟩ := h x hx
  exact hm g (hGF hg) hgx ▸ hg

theorem nonempty_maximal [T0Space X] {F : Set X} (hF : IsClosed F) (hne : F.Nonempty) :
    Nonempty {x : X // x ∈ F ∧ ∀ x' : X, x' ∈ F → x' ⤳ x → x' = x} := by
  obtain ⟨G, hG, hGF, h⟩ := exists_finite_generic hF
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g₀, hg₀, -⟩ := h x hx
  obtain ⟨g, hg⟩ := hG.exists_maximalFor (fun g : X => closure ({g} : Set X)) G ⟨g₀, hg₀⟩
  refine ⟨⟨g, hGF hg.1, fun x' hx' hs => ?_⟩⟩
  obtain ⟨g', hg', hs'⟩ := h x' hx'
  have h1 := hg.2 hg' (specializes_iff_closure_subset.1 (hs'.trans hs))
  exact (hs.antisymm ((specializes_iff_closure_subset.2 h1).trans hs')).eq

theorem mem_of_maximal {x : X} (hx : ∀ x' : X, x' ⤳ x → x' = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) :
    x ∈ U := by
  obtain ⟨G, hG, -, h⟩ := exists_finite_generic (isClosed_univ (X := X))
  have hC : IsClosed (⋃ g ∈ G \ {x}, closure ({g} : Set X)) :=
    (hG.subset Set.diff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨y, hy, hyU⟩ := hd.inter_open_nonempty _ hC.isOpen_compl ⟨x, fun hm => by
    obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 hm
    exact hg.2 (hx g (specializes_iff_mem_closure.2 hgx))⟩
  obtain ⟨g, hg, hgy⟩ := h y trivial
  by_cases e : g = x
  · exact (e ▸ hgy).mem_open hU hyU
  · exact absurd (Set.mem_iUnion₂.2 ⟨g, ⟨hg, e⟩, specializes_iff_mem_closure.1 hgy⟩) hy

end Top

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isProper_toroidalModel_structureMap (Z : Mdl Y i₀) : IsProper Z.s := by
  have := isProper_str (Z.i.c.V W) Z.n
  unfold Pre.s
  infer_instance

theorem noetherianSpace (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : NoetherianSpace Z.X := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp
    (mem_nonunits_V Z.i.c hp hW)).1
  haveI := isProper_toroidalModel_structureMap Z
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  haveI : IsNoetherian Z.X := {}
  infer_instance

theorem nonempty_model (h1 : 1 ≤ Dw.p + Dw.q) (Z : Mdl Y i₀) : Nonempty Z.X := by
  obtain ⟨⟨C⟩, -, h, -⟩ := GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg E H Dw Z.i.l (Xo Z.i.l) Z.i.c h1
  obtain ⟨P, -⟩ := h C
  obtain ⟨g, -⟩ := Descent.exists_tie_frame (Z := Y Z.i) P rfl
  obtain ⟨w, -⟩ := Z.bij _ _ _ (Descent.ptF_snd P) g.v ⟨fun τ i => ⟨g.tan τ i, g.eig τ i⟩, g.basis⟩
  exact ⟨w (IsLocalRing.closedPoint _)⟩

theorem not_inQ_iff (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) :
    ¬ Z.inQ x ↔ (p : Z.X.residueField x) = 0 := by
  constructor
  · intro h
    by_contra hne
    apply h
    let φ : Z.i.c.V W →+* Z.X.residueField x :=
      (Z.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Z.s)
    obtain ⟨q, hq⟩ := CharP.exists (Z.X.residueField x)
    rcases CharP.char_is_prime_or_zero (Z.X.residueField x) q with hqp | rfl
    · exfalso
      have hpq : p ≠ q := by
        rintro rfl
        exact hne (CharP.cast_eq_zero _ _)
      have hco : IsCoprime (p : Z.i.c.V W) (q : Z.i.c.V W) := by
        exact_mod_cast (Nat.Coprime.cast (R := Z.i.c.V W) ((Nat.coprime_primes hp hqp).2 hpq))
      have hpn : ¬ IsUnit (p : Z.i.c.V W) := by
        have := mem_nonunits_V Z.i.c hp.ne_zero hW
        have h2 := (ValuationSubring.coe_mem_nonunits_iff (A := Z.i.c.V W) (a := (p : Z.i.c.V W))).1 (by simpa using this)
        exact h2
      obtain ⟨a, b, hab⟩ := hco
      have hqu : IsUnit (q : Z.i.c.V W) := by
        rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
        · exact absurd (isUnit_of_mul_isUnit_right h) hpn
        · exact isUnit_of_mul_isUnit_right h
      have := hqu.map φ
      rw [map_natCast, CharP.cast_eq_zero] at this
      exact not_isUnit_zero this
    · exact CharP.charP_to_charZero _
  · intro h hc
    haveI : CharZero (Z.X.residueField x) := hc
    exact hp.ne_zero (by exact_mod_cast h)

theorem setOf_not_inQ (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) :
    {x : Z.X | ¬ Z.inQ x} = (Z.genO : Set Z.X)ᶜ := by
  ext x
  rw [Set.mem_setOf_eq, not_inQ_iff hp hW, ← map_natCast (Z.X.evaluation ⊤ x trivial).hom]
  exact Scheme.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) Z.X x trivial _

theorem nonempty_special (h1 : 1 ≤ Dw.p + Dw.q) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) :
    ((Z.genO : Set Z.X)ᶜ).Nonempty := by
  haveI := isProper_toroidalModel_structureMap Z
  obtain ⟨x⟩ := nonempty_model h1 Z
  have hc : IsClosed (Set.range Z.s) := Z.s.isClosedMap.isClosed_range
  obtain ⟨y, hy⟩ : IsLocalRing.closedPoint (Z.i.c.V W) ∈ Set.range Z.s :=
    (IsLocalRing.specializes_closedPoint (Z.s x)).mem_closed hc ⟨x, rfl⟩
  refine ⟨y, fun hm => ?_⟩
  have e : Z.genO = Z.s ⁻¹ᵁ (Sp (Z.i.c.V W)).basicOpen ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv (p : Z.i.c.V W)) := by
    rw [Scheme.preimage_basicOpen_top, map_natCast, map_natCast]
    rfl
  rw [e, basicOpen_eq_of_affine] at hm
  have hm' : Z.s y ∈ PrimeSpectrum.basicOpen (p : Z.i.c.V W) := hm
  rw [hy] at hm'
  exact hm' ((ValuationSubring.coe_mem_nonunits_iff (A := Z.i.c.V W) (a := (p : Z.i.c.V W))).1
    (by simpa using mem_nonunits_V Z.i.c hp.ne_zero hW))

theorem abP_of_isGenP (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) (hx : Z.isGenP x) :
    Z.abP x := by
  haveI := noetherianSpace hp hW Z
  have ho : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2
  obtain ⟨z, hz⟩ := mem_of_maximal hx ho Z.dense
  have : (Y Z.i).jQ z ∈ pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype) ⁻¹' abLocus (Y Z.i).t.G := by
    rw [(Y Z.i).ab_gen]
    exact ⟨z, rfl⟩
  unfold Mdl.abP
  rw [← hz]
  exact this

theorem isFiniteQC_toMod (Z : Mdl Y i₀) (F : Z.Sh) : GlobalTheory.QCoh.IsFiniteQC F.toMod := by
  have h : ∀ a m, GlobalTheory.QCoh.IsFiniteQC (Z.free a m) := fun a m =>
    GlobalTheory.Twist.isFiniteQC_twist (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB _ _ _) _)
  haveI := h F.a F.m
  haveI := h F.a' F.m'
  exact GlobalTheory.QCoh.isFiniteQC_cokernel F.φ

theorem nrm_nonneg (Z : Mdl Y i₀) (F : Z.X.Modules) (f : Γ(F, Z.genO)) (y : Z.Pt) : 0 ≤ Mdl.nrm F f y :=
  Real.sSup_nonneg (by
    rintro r ⟨U, -, h, k, g, lam, -, rfl⟩
    positivity)

theorem nrm_le_one (hp : p ≠ 0) (Z : Mdl Y i₀) (F : Z.X.Modules) [F.IsQuasicoherent] (g₀ : Γ(F, ⊤)) (y : Z.Pt) :
    Mdl.nrm F ((F.presheaf.map (homOfLE (le_top : Z.genO ≤ ⊤)).op).hom g₀) y ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro r ⟨U, hU, h, k, g, lam, hg, rfl⟩
  set g₁ : Γ(F, U) := (F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g₀ with hg₁
  have e : U ⊓ Z.genO = Z.X.basicOpen ((p : ℕ) : Γ(Z.X, U)) := by
    rw [← map_natCast (Z.X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom, Scheme.basicOpen_res]
    rfl
  obtain ⟨n, hn⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU _ inf_le_left e (g - p ^ k • g₁) (by
    rw [map_sub, map_nsmul, sub_eq_zero]
    refine hg.trans (congrArg _ ?_)
    rw [hg₁]
    change (F.presheaf.map _ ≫ F.presheaf.map _).hom g₀ = (F.presheaf.map _ ≫ F.presheaf.map _).hom g₀
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl)
  have h2 := congrArg lam hn
  rw [map_smulₛₗ, map_zero, map_sub, map_nsmul, map_pow, map_natCast, smul_eq_mul] at h2
  have hp' : ((p : ↥(intO ↥y.C.S))) ≠ 0 := Nat.cast_ne_zero.2 hp
  have h3 : lam g = p ^ k • lam g₁ := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ hp'))
  have h4 : ‖((lam g₁ : ↥(intO ↥y.C.S)) : ↥y.C.S)‖ ≤ 1 := (lam g₁).2
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [h3, nsmul_eq_mul]
  push_cast
  rw [norm_mul, norm_pow, y.C.norm_p, mul_right_comm, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
  exact h4

end Free

theorem lawSt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ), ∀ ct : At S κ p, LawSt ct := by
  intro D A N j S κ p ct
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by have := S.rank_eq; have := S.two_le; omega
  refine ⟨fun F f y => nrm_nonneg _ _ f y, ?_, fun l => ?_, fun x hx => abP_of_isGenP ct.hp.ne_zero ct.hW _ x hx,
    fun Z => ?_, fun Z => ?_, ?_⟩
  · rintro Z F f ⟨g₀, rfl⟩ y
    haveI := isFiniteQC_toMod Z F
    exact nrm_le_one ct.hp.ne_zero Z F.toMod g₀ y
  · have h := GlobalTheory.T.graded_line_bundle_exists _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY ct.isYY.2.1 (ct.expo l)
    have hv := GlobalTheory.VB.isVB_toMod h.choose_spec.1
    haveI := hv.isFiniteQC
    obtain ⟨e⟩ := GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY (GlobalTheory.LB.toMod h.choose)
    unfold At.IsInv At.Lb
    rw [dif_pos h]
    exact hv.of_iso e.symm
  · haveI := noetherianSpace ct.hp.ne_zero ct.hW Z
    exact finite_maximal (F := {x : Z.X | ¬ Z.inQ x}) (by
      rw [setOf_not_inQ ct.hp ct.hW]; exact Z.genO.2.isClosed_compl)
  · haveI := noetherianSpace ct.hp.ne_zero ct.hW Z
    exact nonempty_maximal (F := {x : Z.X | ¬ Z.inQ x}) (by
      rw [setOf_not_inQ ct.hp ct.hW]; exact Z.genO.2.isClosed_compl) (by
      rw [setOf_not_inQ ct.hp ct.hW]; exact nonempty_special h1 ct.hp ct.hW Z)
  · intro Z y c c' hc a
    have e : c' = A.H.bar c := by
      apply RingOfIntegers.ext
      rw [hc, A.H.bar_eq]
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    subst e
    rfl

end GlobalTheory.LocM.SharedLaws
