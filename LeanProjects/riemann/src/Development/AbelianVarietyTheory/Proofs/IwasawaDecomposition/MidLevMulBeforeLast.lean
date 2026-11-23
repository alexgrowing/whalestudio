import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongAtOfNearSame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

theorem last_rep_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∃ b : (I.idx a).β (B.R.m - 1), ∀ P, (I.idx a).h (B.R.m - 1) b P = 1 := by
  have hL := hOk.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  rw [e]
  obtain ⟨b, -⟩ := hL.last_uniq
  exact ⟨b, hL.last_h b⟩

theorem prCat_last_le_GLint {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have h := (hOk.idx_ok a).int (B.R.m - 1) b P
  rwa [hb P] at h

theorem inv_mul_rearrange {G : Type*} [Group G] (A B C D : G) : (A * B)⁻¹ * (C * D) = (B⁻¹ * D) * (D⁻¹ * (A⁻¹ * C) * D) := by
  group

theorem nearAt_prod_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ex ey : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (rg rg' : GL (Fin N) E)
    (hx : GlobalTheory.TwU.CongAt P n (ex⁻¹ * GlobalTheory.TwU.ratA F rg)) (hy : GlobalTheory.TwU.CongAt P n (ey⁻¹ * GlobalTheory.TwU.ratA F rg'))
    (hint : ∀ a b, IntAt P ((rg' : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((rg'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.CongAt P n ((ex * ey)⁻¹ * GlobalTheory.TwU.ratA F (rg * rg')) := by
  rw [map_mul, inv_mul_rearrange]
  exact GlobalTheory.CplPt.congAt_mul _ hy (GlobalTheory.CplPt.congAt_conj _ hx hint)

theorem nearV_mul_pairs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) (x y : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P y g' z' → GlobalTheory.Mem.Col2.QChi.NearV I l Z a v P (x * y) (g * g') := by
  intro B X I hOk l Z a v P x y g g' z z' hx hy
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
    (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g').1 ⟨z', hy.1⟩
  have hint := prCat_last_le_GLint I hOk a P hg'
  have hx2 := hx.2
  have hy2 := hy.2
  unfold NearV GlobalTheory.TwU.NearAt at hx2 hy2 ⊢
  have key := nearAt_prod_of_conj _ _ _ _ _ _ hx2 hy2 (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hint⟩)
  rw [map_mul (GlobalTheory.Mem.Col2.ChartLevel.emb v)]
  erw [map_mul (GlobalTheory.TwU.seamGL (sm I l Z)) g g']
  exact key

theorem chiInv_last_eq_char {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    ∃ φ : ↥(prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1) →* B.fields.Kˣ,
      ∀ r ∈ Loc.Cbe (Jat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1) 1,
      ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
      (∀ x, r (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) = Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) (g x)) →
      chiInv I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 r = φ ⟨g, hg⟩ := by
  have hL := hOk.idx_ok a
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have hint := prCat_last_le_GLint I hOk a P
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        GlobalTheory.TopStep.redGL _ P.1 ⟨g, hint hg⟩ ∈ ((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).H := fun g hg =>
      (hL.grpG _ b ⟨P.1, hP⟩ _).2 ⟨g, by rw [hb]; exact hg, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx⟩
    refine ⟨((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).lam.comp
      (MonoidHom.codRestrict ((GlobalTheory.TopStep.redGL _ P.1).comp (Subgroup.inclusion hint)) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrG (B.R.m - 1) b ⟨P.1, hP⟩ ⟨_, hH g hg⟩ g r (by rw [hb]; exact hr) hrx
      (fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx)
    rw [hb] at hc
    exact hc.symm
  · classical
    have hQ := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        (⟨g, hint hg⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1)) ∈ ((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).H := fun g hg => by
      rw [hL.grpQ _ b ⟨P.1, hQ⟩, hb]
      exact Subgroup.mem_subgroupOf.2 hg
    refine ⟨((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).lam.comp
      (MonoidHom.codRestrict (Subgroup.inclusion hint) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrQ (B.R.m - 1) b ⟨P.1, hQ⟩ ⟨⟨g, hint hg⟩, hH g hg⟩ r (by rw [hb]; exact hr) hrx
    rw [hb] at hc
    exact hc.symm

theorem midLev_mul_beforeLast : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g' z' → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 (g * g') (z * z') := by
  intro B X I hOk a P g g' z z' ⟨r, hr, hrx, hz⟩ ⟨r', hr', hrx', hz'⟩
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  have hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r, hr, hrx⟩
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r', hr', hrx'⟩
  have hrr : ∀ x, (r * r') (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) =
      Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) ((g * g') x) := fun x => by
    rw [LinearEquiv.mul_apply, hrx', hrx]
    rfl
  refine ⟨r * r', mul_mem hr hr', hrr, ?_⟩
  rw [hz, hz', hφ r hr g hg hrx, hφ r' hr' g' hg' hrx', hφ (r * r') (mul_mem hr hr') (g * g') (mul_mem hg hg') hrr,
    ← Units.val_mul, ← map_mul]
  rfl

theorem midLev_one_last : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 1 1 := by
  intro B X I hOk a P
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  refine ⟨1, one_mem _, fun x => rfl, ?_⟩
  rw [hφ 1 (one_mem _) 1 (one_mem _) (fun x => rfl)]
  exact (congrArg Units.val (map_one φ)).symm

theorem nearV_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV GlobalTheory.TwU.NearAt
  erw [map_one (GlobalTheory.TwU.seamGL (sm I l Z)), map_one, map_one, inv_one, one_mul]
  exact GlobalTheory.TwU.congAt_one _ _

open Classical in
theorem valV_factor {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (P : SBof I a) (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K)
    (hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) (hn : NearPair I l Z a v P x g z) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = z := by
  rw [dif_pos ⟨hP, g, z, hn⟩]
  exact GlobalTheory.Mem.Col2.QChi.nearPair_val_unique I hOk l Z a v P x _ g _ z (Exists.choose_spec (Exists.choose_spec (⟨hP, g, z, hn⟩ : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z).2)) hn

open Classical in
theorem valV_factor_off {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (P : SBof I a) (hP : ¬ IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = 1 :=
  dif_neg fun h => hP h.1

theorem valV_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), GlobalTheory.Mem.Col2.QChi.valV I l Z a v 1 = 1 ∧ ∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → GlobalTheory.Mem.Col2.QChi.valV I l Z a v (x * y) = GlobalTheory.Mem.Col2.QChi.valV I l Z a v x * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y := by
  intro B X I hOk l Z a v
  constructor
  · unfold valV
    rw [Finset.prod_eq_one, map_one]
    intro P _
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · exact valV_factor I hOk l Z a v 1 P 1 1 hP ⟨midLev_one_last I hOk a P, nearV_one_one I l Z a v P⟩
    · exact valV_factor_off I l Z a v 1 P hP
  · intro x y hx hy
    unfold valV
    rw [← map_mul, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · have hx' : ∃ g z, NearPair I l Z a v P x g z := hx P hP
      have hy' : ∃ g z, NearPair I l Z a v P y g z := hy P hP
      obtain ⟨g, z, hgz⟩ := hx'
      obtain ⟨g', z', hgz'⟩ := hy'
      have hxy : NearPair I l Z a v P (x * y) (g * g') (z * z') := ⟨midLev_mul_beforeLast I hOk a P g g' z z' hgz.1 hgz'.1, nearV_mul_pairs I hOk l Z a v P x y g g' z z' hgz hgz'⟩
      rw [valV_factor I hOk l Z a v (x * y) P _ _ hP hxy, valV_factor I hOk l Z a v x P _ _ hP hgz, valV_factor I hOk l Z a v y P _ _ hP hgz']
    · rw [valV_factor_off I l Z a v (x * y) P hP, valV_factor_off I l Z a v x P hP, valV_factor_off I l Z a v y P hP, mul_one]

end GlobalTheory.Mem.Col2.QChi

end
