import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterAtQFiniteOrderAndTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruence
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.XStepOrb
open GlobalTheory.Mem.Col2.TopCh
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs)

theorem snd_eq (p : (stepX Ch sel mu P).D ()) : p.1.2 = ∅ := p.2

theorem pt_ext {p q : (stepX Ch sel mu P).D ()} (h : p.1.1 = q.1.1) : p = q :=
  Subtype.ext (Prod.ext h ((snd_eq Ch sel mu P p).trans (snd_eq Ch sel mu P q).symm))

def mkPt (p : XPt Pr R sel mu) : (stepX Ch sel mu P).D () := ⟨(p, ∅), rfl⟩

theorem orbit_inj (c c' : (stepX Ch sel mu P).Cl) (γ : UF X.E (R.N R.m - 1)) (h : (rowTyG Ch P).grp) (θ : (levQX R sel mu).grp)
    (e : ((γ, h.1, θ.1) : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) Pr.vGs × GLQ X.E (R.N R.m - 1) (QE sel (mu : Chr X.F X.E X.K))) • ((stepX Ch sel mu P).rep c).1.1 = ((stepX Ch sel mu P).rep c').1.1) : c = c' := by
  obtain ⟨⟨⟩, q⟩ := c
  obtain ⟨⟨⟩, q'⟩ := c'
  have h1 : ((γ, h, θ) : (stepX Ch sel mu P).G ()) • (stepX Ch sel mu P).rep ⟨(), q⟩ = (stepX Ch sel mu P).rep ⟨(), q'⟩ :=
    pt_ext Ch sel mu P e
  have h2 := (stepX Ch sel mu P).rp_spec () q
  have h3 := (stepX Ch sel mu P).rp_spec () q'
  congr 1
  rw [← h2, ← h3]
  have h4 : (MulAction.orbitRel ((stepX Ch sel mu P).G ()) ((stepX Ch sel mu P).D ())) ((stepX Ch sel mu P).rp () q') ((stepX Ch sel mu P).rp () q) := ⟨_, h1⟩
  exact (Quotient.sound h4).symm

theorem orbit_surj (p : XPt Pr R sel mu) : ∃ (c : (stepX Ch sel mu P).Cl) (γ : UF X.E (R.N R.m - 1)) (h : (rowTyG Ch P).grp) (θ : (levQX R sel mu).grp),
    ((γ, h.1, θ.1) : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) Pr.vGs × GLQ X.E (R.N R.m - 1) (QE sel (mu : Chr X.F X.E X.K))) • ((stepX Ch sel mu P).rep c).1.1 = p := by
  obtain ⟨g, hg⟩ := (stepX Ch sel mu P).exists_mv () (mkPt Ch sel mu P p)
  exact ⟨_, g.1, g.2.1, g.2.2, congrArg (fun q : (stepX Ch sel mu P).D () => q.1.1) hg⟩

theorem stab_iff (c : (stepX Ch sel mu P).Cl) (γ : UF X.E (R.N R.m - 1)) :
    (∃ s : (stepX Ch sel mu P).Stab c, s.1.1 = γ) ↔ ∃ (h : (rowTyG Ch P).grp) (θ : (levQX R sel mu).grp),
      ((γ, h.1, θ.1) : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) Pr.vGs × GLQ X.E (R.N R.m - 1) (QE sel (mu : Chr X.F X.E X.K))) • ((stepX Ch sel mu P).rep c).1.1 = ((stepX Ch sel mu P).rep c).1.1 := by
  obtain ⟨⟨⟩, q⟩ := c
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.1.2.1, s.1.2.2, congrArg (fun q : (stepX Ch sel mu P).D () => q.1.1) (MulAction.mem_stabilizer_iff.1 s.2)⟩
  · rintro ⟨h, θ, e⟩
    exact ⟨⟨(γ, h, θ), MulAction.mem_stabilizer_iff.2 (pt_ext Ch sel mu P e)⟩, rfl⟩

theorem lev_iff (c : (stepX Ch sel mu P).Cl) (q : XPt Pr R sel mu) :
    (∃ κ : (stepX Ch sel mu P).G c.1, (stepX Ch sel mu P).gam c.1 κ = 1 ∧ ((stepX Ch sel mu P).act c.1 κ ((stepX Ch sel mu P).rep c)).1.1 = q) ↔
      ∃ (h : (rowTyG Ch P).grp) (θ : (levQX R sel mu).grp),
      ((1, h.1, θ.1) : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) Pr.vGs × GLQ X.E (R.N R.m - 1) (QE sel (mu : Chr X.F X.E X.K))) • ((stepX Ch sel mu P).rep c).1.1 = q := by
  obtain ⟨⟨⟩, c⟩ := c
  constructor
  · rintro ⟨κ, hγ, e⟩
    have h1 : κ.1 = 1 := Subtype.ext ((toGLm X.E (R.N R.m - 1)).injective (hγ.trans (map_one _).symm))
    refine ⟨κ.2.1, κ.2.2, ?_⟩
    rw [← e, ← h1]
    rfl
  · rintro ⟨h, θ, e⟩
    exact ⟨(1, h, θ), map_one (ufGL X.E (R.N R.m - 1)), e⟩

end GlobalTheory.Mem.Col2.XStepOrb

namespace GlobalTheory.Mem.Col2.TC
open GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.Col2.XStepOrb

set_option maxHeartbeats 4000000 in

theorem memberLevel_read {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (KP : ClsPTied (D := I.rec7 l Z) u) [NeZero (B.R.N B.R.m - 1)]
    (hR : I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1)) :
    (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m - 1), x ∈ KP.lev.U ↔ x ∈ levU B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs (rowTyG I.Ch I.Ps).grp) ∧
    ∀ (x : KP.lev.U) (z : J0 B.sp.cm (B.R.N B.R.m - 1) ∅) (h : (rowTyG I.Ch I.Ps).grp), z.1 = x.1 →
      redG B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs z = h.1⁻¹ → KP.lev.chi x = Units.map (B.embLL : B.fields.K →* ℂ) ((rowTyG I.Ch I.Ps).chr h) := by
  classical
  have hQ0 : I.Q I.mu0 = ∅ := (GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).1
  obtain ⟨c0, -⟩ := KP.y_bij.2 (Quotient.mk'' 1)
  let g0 : GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E) := (KP.y c0).1
  have hp0 : IsPtOf B.sp.cm g0 ((I.stX I.mu0).rep c0).1.1 := hR.pt c0

  have hmv : ∀ (z : GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E)) (hz : z ∈ J0 B.sp.cm (B.R.N B.R.m - 1) ∅) (h : (rowTyG I.Ch I.Ps).grp),
      redG B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs ⟨z, hz⟩ = h.1⁻¹ →
      IsPtOf B.sp.cm (g0 * z) (((1, h.1, 1) : UF B.host.E (B.R.N B.R.m - 1) × GLG B.host.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m - 1) (I.Q I.mu0)) • ((I.stX I.mu0).rep c0).1.1) :=
    fun z hz h hr => (isPtOf_mul_J0 _ _ B.sp.cm _ ∅ (B.primes X).vGs (I.Q I.mu0) g0 z ((I.stX I.mu0).rep c0).1.1
      ((I.stX I.mu0).rep c0).1.1 h.1).2.1 hQ0 hp0 hz hr
  refine ⟨fun x hx => ⟨fun hxU => ?_, fun hxL => ?_⟩, fun x z h e hr => ?_⟩
  · obtain ⟨q, hq⟩ := (isPtOf_mul_J0 _ _ B.sp.cm _ ∅ (B.primes X).vGs (I.Q I.mu0) (g0 * x) 1 ((I.stX I.mu0).rep c0).1.1
      ((I.stX I.mu0).rep c0).1.1 1).2.2 hQ0 (mul_mem hp0.uni hx)
    obtain ⟨h, θ, e⟩ := (lev_iff I.Ch I.sel (I.tup I.mu0) I.Ps c0 q).1 ((hR.lev c0 x q hq).1 hxU)
    obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 _ _ B.sp.cm _ ∅ (B.primes X).vGs (I.Q I.mu0) g0 x ((I.stX I.mu0).rep c0).1.1 q h.1).1
      hp0 hq).2 (by rw [← e]; rfl)
    exact (mem_levU _ _ _ _ _).2 ⟨hz, by rw [hr]; exact inv_mem h.2⟩
  · obtain ⟨hz, hr⟩ := (mem_levU _ _ _ _ _).1 hxL
    have h1 := hmv x hz ⟨_, inv_mem hr⟩ (inv_inv _).symm
    exact (hR.lev c0 x _ h1).2 ((lev_iff I.Ch I.sel (I.tup I.mu0) I.Ps c0 _).2 ⟨⟨_, inv_mem hr⟩, 1, rfl⟩)
  · have hz : (x.1 : GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E)) ∈ J0 B.sp.cm (B.R.N B.R.m - 1) ∅ := e ▸ z.2
    have hr' : redG B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs ⟨x.1, hz⟩ = h.1⁻¹ := by
      rw [← hr]; congr 1; exact Subtype.ext e.symm
    have h1 := hmv x.1 hz h hr'
    have h2 := hR.chr c0 x ((1, h, 1) : (I.stX I.mu0).G c0.1) (map_one (ufGL B.fields.E (B.R.N B.R.m - 1))) h1
    apply Units.ext
    refine h2.trans ?_
    show B.embLL (((rowTyG I.Ch I.Ps).chr h * (levQX B.R I.sel (I.tup I.mu0)).chr 1 : B.fields.Kˣ) : B.fields.K) = _
    rw [map_one, mul_one]
    rfl

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC
open GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.Col2.XStepOrb GlobalTheory.TopStep GlobalTheory.Mem.ColAd

local instance neZero_rankXp (R : Ranks) : NeZero (R.N R.m - 1) := ⟨by have := rank_X'_eq R; have := rSym_rSD R; unfold rSym at this; omega⟩

set_option maxHeartbeats 20000000 in

theorem tuplePrimedSpace_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (KP : ClsPTied (D := I.rec7 l Z) u), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) → ∃ K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q), K.lev.Lb = KP.lev.Lb ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) ∧ I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) ∧ (∀ v ∈ badG (I.rec7 l Z), K.lev.Uloc v = KP.lev.Uloc v) ∧ ∀ (κ : K.lev.U) (κ' : KP.lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → K.lev.chi κ = KP.lev.chi κ' := by
  intro B X I hI hP l Z u a Q KP hQ hQ2 hR
  classical
  have hJ : gramP (I.rec7 l Z) = 1 := (spaces_in_coordinates I hI hP l Z).2.1
  have hQp : ∀ P ∈ I.Q a, P ∉ (∅ : Finset (HeightOneSpectrum (𝓞 B.host.E))) ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (∅ : Finset (HeightOneSpectrum (𝓞 B.host.E))) ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a := fun P hP => by
    obtain ⟨⟨-, h2, -, h4, h5⟩, -⟩ := (GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a P hP
    exact ⟨Finset.notMem_empty _, h2, Finset.notMem_empty _, h4, h5⟩
  have hconj : ∀ P ∈ uSG (∅ : Finset (HeightOneSpectrum (𝓞 B.host.E))) (uSG (B.primes X).vGs (I.Q a)),
      conjPrime₂ P ∉ uSG (∅ : Finset (HeightOneSpectrum (𝓞 B.host.E))) (uSG (B.primes X).vGs (I.Q a)) := by
    intro P hP hc
    simp only [uSG, Finset.empty_union, Finset.mem_union] at hP hc
    rcases hP with hP | hP
    · have hs := (levOk_base B X).split P (by simp [uSG, hP])
      rcases hc with hc | hc
      · exact hs (by simp [uSG, hc])
      · exact (hQp _ hc).2.2.2.1 (by rw [rlh_conjP_conjP]; exact hP)
    · rcases hc with hc | hc
      · exact (hQp P hP).2.2.2.1 hc
      · exact (hQp P hP).2.2.2.2 hc
  have hex : ∀ c : (I.stX a).Cl, ∃ g, IsPtOf B.sp.cm g ((I.stX a).rep c).1.1 := fun c =>
    PtExist.exists_isPtOf_cm B.sp.cm _ ∅ (B.primes X).vGs (I.Q a) _ (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _)
      (Finset.disjoint_left.2 fun P h1 h2 => (hQp P h2).2.1 h1) hconj
  choose y hy using hex
  have hy1 : ∀ c, IsPtOf B.sp.cm (y c * (1 * 1)) ((I.stX a).rep c).1.1 := fun c => by rw [mul_one, mul_one]; exact hy c
  let d : I.Q a → B.host.E := fun P => ((qOf P.1 : ℕ) : B.host.E) ^ 1
  choose N hN using fun P : I.Q a => exists_dep_eq_exp P.1 1
  have hd : ∀ P, d P ≠ 0 := fun P => pow_ne_zero _ qOf_ne_zero
  have hdN : ∀ P : I.Q a, P.1.valuation B.host.E (d P) ≤ WithZero.exp (-(N P : ℤ)) := fun P => (hN P).le
  have hΘ : ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m - 1) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m - 1) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m - 1)) → ∃ h : g ∈ (levQX B.R I.sel (I.tup a) P).H, (levQX B.R I.sel (I.tup a) P).lam ⟨g, h⟩ = 1 := by
    intro P g hg
    have hk : g ∈ prinCong (B.R.N B.R.m - 1) P.1 1 := mem_prinCong_of_sm g (sm_of_lqPrinc (hN P) hg)
    have h1 : redGL (B.R.N B.R.m - 1) P.1 g = 1 := redGL_of_prinCong one_pos hk
    have hm : g ∈ (levQX B.R I.sel (I.tup a) P).H := by
      rw [mem_levQX, h1]; exact one_mem _
    refine ⟨hm, ?_⟩
    rw [levQX_lam]
    have e : (⟨redGL (B.R.N B.R.m - 1) P.1 g, hm⟩ : (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)) P).H) = 1 := Subtype.ext h1
    rw [e, map_one]
  let gm : ∀ c, (I.stX a).Stab c →* UF B.host.E (B.R.N B.R.m - 1) := fun c => (MonoidHom.fst _ _).comp (Subgroup.subtype _)
  let ψ := topChi B.embLL KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d hd N hdN hΘ
  obtain ⟨hU, hχ⟩ := memberLevel_read I hI l Z u KP hR
  have hU1 : ∀ x ∈ UAd B.sp.cm (B.R.N B.R.m - 1), x ∈ KP.lev.U ↔ (1 : GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E))⁻¹ * x * 1 ∈ levU B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs (rowTyG I.Ch I.Ps).grp :=
    fun x hx => (hU x hx).trans (by rw [inv_one, one_mul, mul_one])
  have hψ : ∀ x : topU KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d, (∀ P : I.Q a, rhoP B.host.F P.1 x.1 = 1) → ψ x = 1 :=
    (topChi_finite_order_and_trivial _ _ B.fields.K _ _ B.embLL KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d hd N hdN hΘ).2
  have hQv : ∀ v, v ∈ Q ↔ ∃ P ∈ I.Q a, P.under (𝓞 B.host.F) = v := hQ
  have hTQ : ∀ v ∈ Q, ((1 : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := fun v _ h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by rw [Nat.cast_one] at h; exact h))
  have hLbE : KP.lev.Lb = baseLb B.fields.E (B.R.N B.R.m - 1) ∅ := by
    rw [show baseLb B.fields.E (B.R.N B.R.m - 1) ∅ = stdLat B.fields.E (B.R.N B.R.m - 1) from RowTie.L_empty _]
    ext x
    constructor
    · intro h
      exact (mem_stdLat x).2 fun j => let ⟨r, hr, _⟩ := (hR.lb x).1 h j; ⟨r, hr.symm⟩
    · intro h
      exact (hR.lb x).2 fun j => let ⟨r, hr⟩ := (mem_stdLat x).1 h j; ⟨r, hr.symm, fun _ => one_dvd r⟩
  have hlatS : ∀ x : Fin (B.R.N B.R.m - 1) → (I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F, x ∈ latS (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) (tensInt (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) (intOE (I.rec7 l Z).host.E) (intAd (I.rec7 l Z).host.F)) KP.lev.Lb ↔ ((1 : GL (Fin (B.R.N B.R.m - 1)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E))⁻¹ : GL (Fin (B.R.N B.R.m - 1)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)).1 *ᵥ x ∈ latS (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) (tensInt (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) (intOE (I.rec7 l Z).host.E) (intAd (I.rec7 l Z).host.F)) (baseLb (I.rec7 l Z).host.E (B.R.N B.R.m - 1) ∅) := fun x => by
    rw [hLbE, inv_one, Units.val_one, Matrix.one_mulVec]
    exact Iff.rfl
  have hinj := fun c c' γ h θ e => orbit_inj I.Ch I.sel (I.tup a) I.Ps c c' γ h θ e
  obtain ⟨C', hLb, hCU, hloc, hchi, hy', hst⟩ := exists_clsG_top B.host.F B.host.E B.fields.K B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs (I.Q a)
    (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f (badG (I.rec7 l Z)) KP.lev Q (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup a)) 1 d hd N hdN hΘ 1 1
    (I.stX a).Cl (fun c => ((I.stX a).rep c).1.1) y (I.stX a).Stab (fun c => ((I.stX a).rep c).1.1.deco.1.N) gm ψ hJ
    hQv hTQ hQp (fun _ => rfl) (one_mem _) (fun _ => map_one _) (one_mem _) hU1 hlatS hy1 hinj
    (fun p => orbit_surj I.Ch I.sel (I.tup a) I.Ps p) (fun c => (RowTie.L_empty _).symm)
    (fun c s t e => by
      letI := (I.stX a).actD c.1
      have h1 := MulAction.mem_stabilizer_iff.1 (s⁻¹ * t).2
      have e' : s.1.1 = t.1.1 := e
      have h2 : (I.stX a).gam c.1 (s⁻¹ * t).1 = 1 := by
        show ufGL B.fields.E (B.R.N B.R.m - 1) (s.1⁻¹ * t.1).1 = 1
        rw [Prod.fst_mul, Prod.fst_inv, e', inv_mul_cancel, map_one]
      have h3 := (l.per u a).step.stab_inj c.1 _ _ h1 h2
      exact inv_mul_eq_one.1 (Subtype.ext h3))
    (fun c γ => (exists_congr fun s => Iff.rfl).trans (stab_iff I.Ch I.sel (I.tup a) I.Ps c γ)) hψ
  let K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q) :=
    { lev := C'.lev, y := C'.y, y_bij := C'.y_bij, lat := fun c => ((I.stX a).rep c).1.1.deco.1.N, y_lat := C'.y_lat,
      lat_fin := fun c => (Module.Finite.iff_fg (R := 𝓞 (I.rec7 l Z).host.E)
        (M := Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).2 ((I.stX a).rep c).1.1.deco.2.lat.fg, stabI := C'.stabI, stabI_inj := C'.stabI_inj, stabI_range := C'.stabI_range }
  have hxU : ∀ x : KP.lev.U, (x.1 : GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E)) ∈ UAd B.sp.cm (B.R.N B.R.m - 1) := fun x => by
    have eU : UPts (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
        UAd B.sp.cm (B.R.N B.R.m - 1) := by rw [hJ]; rfl
    exact eU ▸ ((KP.lev.U_eq x.1).1 x.2).1
  have hfinP : ∃ m, 0 < m ∧ ∀ x : KP.lev.U, KP.lev.chi x ^ m = 1 := by
    obtain ⟨m, hm, hm'⟩ := levFam_chr_exp (rowTyG I.Ch I.Ps)
    refine ⟨m, hm, fun x => ?_⟩
    have h1 := (hU x.1 (hxU x)).1 x.2
    obtain ⟨hz, hr⟩ := (mem_levU _ _ _ _ _).1 h1
    rw [hχ x ⟨x.1, hz⟩ ⟨_, inv_mem hr⟩ rfl (inv_inv _).symm, ← map_pow, hm', map_one]
  have hχ' : ∀ (x : KP.lev.U) (z : J0 B.sp.cm (B.R.N B.R.m - 1) ∅) (h : (rowTyG I.Ch I.Ps).grp), z.1 = (1 : GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E))⁻¹ * (show GL (Fin (B.R.N B.R.m - 1)) (AfE B.host.F B.host.E) from x.1) * 1 → redG B.sp.cm (B.R.N B.R.m - 1) ∅ (B.primes X).vGs z = h.1⁻¹ → KP.lev.chi x = Units.map (B.embLL : B.fields.K →* ℂ) ((rowTyG I.Ch I.Ps).chr h) :=
    fun x z h e e' => hχ x z h (by rw [e, inv_one, one_mul, mul_one]) e'
  refine ⟨K, hLb, ?_, ?_, fun v hv => hloc v fun hvQ => ?_, ?_⟩
  · obtain ⟨m1, hm1, hm1'⟩ := hfinP
    obtain ⟨m2, hm2, hm2'⟩ := (topChi_finite_order_and_trivial _ _ B.fields.K _ _ B.embLL KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d hd N hdN hΘ).1
      (fun P => levQX_root (R := B.R) I.sel (I.tup a) P)
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, fun κ => ?_⟩
    show C'.lev.chi κ ^ (m1 * m2) = 1
    have hκ : κ.1 ∈ topU KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d := hCU ▸ κ.2
    have e1 : KP.lev.chi ⟨κ.1, topU_le _ _ _ _ hκ⟩ ^ (m1 * m2) = 1 := by rw [pow_mul, hm1', one_pow]
    have e2 : ψ ⟨κ.1, hκ⟩ ^ (m1 * m2) = 1 := by rw [mul_comm, pow_mul, hm2', one_pow]
    have e : C'.lev.chi κ = KP.lev.chi ⟨κ.1, topU_le _ _ _ _ hκ⟩ * ψ ⟨κ.1, hκ⟩ := hchi κ _ _ rfl rfl
    rw [e, mul_pow, e1, e2, one_mul]
  · refine ⟨fun x => ?_, fun c => rfl, fun c => ?_, fun c x q hq => ?_, fun c x κ hκ hq => ?_, fun c s => (hst c s).trans rfl⟩
    · show x ∈ C'.lev.Lb ↔ _
      rw [hLb]
      exact hR.lb x
    · show IsPtOf B.sp.cm (C'.y c).1 _
      rw [hy' c]
      exact hy c
    · show x ∈ C'.lev.U ↔ _
      rw [hCU, lev_iff]
      exact mem_topU_iff _ _ B.fields.K B.sp.cm _ ∅ (B.primes X).vGs (I.Q a) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup a)) d hd N hdN hΘ
        KP.lev.U 1 1 (y c) x _ q (one_mem _) (fun _ => map_one _) (one_mem _) hU1 (hy1 c) (by rw [mul_one, mul_one, ← hy' c]; exact hq)
    · have k1 : κ.1 = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N B.R.m - 1)).injective (hκ.trans (map_one _).symm))
      have hκ' : ((I.stX a).act c.1 κ ((I.stX a).rep c)).1.1 = ((1, κ.2.1.1, κ.2.2.1) : UF B.host.E (B.R.N B.R.m - 1) × GLG B.host.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m - 1) (I.Q a)) • ((I.stX a).rep c).1.1 := by
        rw [← k1]; rfl
      have hx : x.1 ∈ topU KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d := hCU ▸ x.2
      have h1 := chi_mul_topChi_moved _ _ B.fields.K B.sp.cm _ ∅ (B.primes X).vGs (I.Q a) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup a)) d hd N hdN hΘ
        B.embLL KP.lev.U KP.lev.chi 1 1 (y c) ((I.stX a).rep c).1.1 (one_mem _) (fun _ => map_one _) (one_mem _) hχ' ⟨x.1, hx⟩ κ.2.1 κ.2.2 (hy1 c)
        (by rw [mul_one, mul_one, ← hy' c, ← hκ']; exact hq)
      show ((C'.lev.chi x : ℂˣ) : ℂ) = _
      rw [hchi x ⟨x.1, topU_le _ _ _ _ hx⟩ ⟨x.1, hx⟩ rfl rfl]
      exact congrArg Units.val h1
  · obtain ⟨j, hj⟩ : ∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      rcases hv with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    exact (hQ2 v hvQ).2 j hj
  · intro κ κ' e hκQ
    show C'.lev.chi κ = KP.lev.chi κ'
    have hκ : κ.1 ∈ topU KP.lev.U 1 (levQX B.R I.sel (I.tup a)) d := hCU ▸ κ.2
    have e4 : C'.lev.chi κ = KP.lev.chi κ' * ψ ⟨κ.1, hκ⟩ := hchi κ κ' ⟨κ.1, hκ⟩ e rfl
    have e5 : ψ ⟨κ.1, hκ⟩ = 1 := hψ ⟨κ.1, hκ⟩ fun P => by
      have hv : P.1.under (𝓞 B.host.F) ∈ Q := (hQv _).2 ⟨P.1, P.2, rfl⟩
      have h1 := hκQ _ hv
      exact (localComponent_congr rfl (h1.trans (map_one _).symm)).trans (map_one _)
    rw [e4, e5]
    exact mul_one _

end GlobalTheory.Mem.Col2.TC

end
