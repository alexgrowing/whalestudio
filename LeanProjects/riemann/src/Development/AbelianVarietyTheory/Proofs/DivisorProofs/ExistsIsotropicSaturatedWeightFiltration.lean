import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleIsometriesCoisotropicKernelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosedStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twistI {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} (hB : D₀.TauBimult) [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (I : TateIsoQ D D₀ oa F) (g : ℕ → D.La ≃ₗ[𝓞 E] D.La) (hiso : ∀ n a b, D.EF (g n a) (g n b) = D.EF a b)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) : TateIsoQ D D₀ oa F where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := I.ev n (g n a)
  add n hn a b := by rw [map_add]; exact I.add n hn _ _
  lin n hn x a := by rw [map_smul]; exact I.lin n hn x _
  ker n hn a b := (I.ker n hn _ _).trans
    ⟨fun ⟨e, he⟩ => ⟨(g n).symm e, by
        have := congrArg (g n).symm he
        rwa [LinearEquiv.symm_apply_apply, map_add, LinearEquiv.symm_apply_apply, map_nsmul] at this⟩,
     fun ⟨e, he⟩ => ⟨g n e, by rw [he, map_add, map_nsmul]⟩⟩
  onto n hn p := by
    obtain ⟨b, hb⟩ := I.onto n hn p
    exact ⟨(g n).symm b, by rw [LinearEquiv.apply_symm_apply]; exact hb⟩
  tower n m hn hm a := by
    obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm (g (n * m) a)
    exact ⟨q, h₁, h₂, GlobalTheory.TorusExt.equiv_trans hB h₃ ((I.ker n hn _ _).2 (htow n m hn hm a))⟩
  isom n hn a b := by rw [← hiso n a b]; exact I.isom n hn _ _

end GlobalTheory.LowFilt

open GlobalTheory.LowFilt GlobalTheory.LowDat in
theorem GlobalTheory.LowFilt.exists_filt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
  1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ Z : Submodule (𝓞 E) Dw.La, GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨tK, ⟨m1⟩, ⟨m2⟩⟩ := C.gen
  haveI : CharZero R := hR.2
  letI := H.starRing
  have hB := C.P.D.tau_bimult
  have hT : C.P.TorsionIso := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  haveI : IsNoetherianRing R := hR.1.1
  let F₀ := AlgebraicClosure (FractionRing R)
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F₀).injective
  obtain ⟨I₀, hI₀⟩ := GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart Xo c R hR C tK m1 m2 F₀
  obtain ⟨y, hy, hcois⟩ := GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel Dw R C.P.D.toPre C.P.oD C.P.D.psi_even hB F₀ I₀
  have htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e := by
    intro n m hn hm a
    obtain ⟨q, h₁, -, z, h₃, -⟩ := I₀.tower n m hn hm a
    obtain ⟨e₁, he₁⟩ := hy (n * m) (Nat.mul_pos hn hm) a
    obtain ⟨e₂, he₂⟩ := hy n hn a
    have e₃ : (q.y : C.P.D.toPre.X) = (I₀.ev (n * m) a).y := h₁
    have e₄ : q.y = (I₀.ev n a).y - n • z := by rw [h₃]; abel
    refine ⟨m • e₁ - e₂ - z, ?_⟩
    rw [he₁, he₂, ← e₃, e₄]
    simp only [smul_sub, smul_smul]
    abel
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨Z, hZ, hZr, g, hgi, hgt, hgN, hker⟩ := GlobalTheory.T.exists_compatible_isometries_coisotropic_kernels Dw y hcois htow (GlobalTheory.T.finrank_uChart_le_min_signature Xo c R hR C) l.M' hM
  refine ⟨Z, hZ, hZr, tK, m1, m2, fun F _ _ _ => ?_⟩
  let I₁ := twistI hB I₀ g hgi hgt
  have hI₁ : XFLevel C tK m1 m2 F₀ I₁ := by
    refine ⟨hI₀.1, fun k a σ hk x hx => hI₀.2 k a σ hk x ?_⟩
    have hk1 : 1 ≤ k ∧ k ∣ l.M' := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨l.A_pos, Nat.dvd_lcm_right _ _⟩
      · exact ⟨by have := l.three_le; omega, Nat.dvd_lcm_left _ _⟩
    obtain ⟨f, f₁, -, f₃, -⟩ := hT F₀ k hk1.1
    rw [f₁] at hx ⊢
    rw [hx]
    refine (f₃ _ _).2 ((I₀.ker k hk1.1 _ _).2 ?_)
    obtain ⟨e, he⟩ := hgN k a
    obtain ⟨j, hj⟩ := hk1.2
    exact ⟨j • e, by rw [smul_smul, ← hj]; exact he⟩
  obtain ⟨I, hIl, hIy⟩ := GlobalTheory.T.exists_levelIsometry_extension_algClosed Xo c R hR C tK m1 m2 I₁ hI₁ F
  refine ⟨I, hIl, fun n hn a => ?_⟩
  rw [GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul R _ hB F n hn, hIy, ← hker n hn a]
  obtain ⟨e, he⟩ := hy n hn (g n a)
  change (∃ e, (I₀.ev n (g n a)).y = n • e) ↔ _
  constructor
  · rintro ⟨e', he'⟩; exact ⟨e + e', by rw [he, he', smul_add, add_comm]⟩
  · rintro ⟨e', he'⟩; exact ⟨e' - e, by rw [smul_sub, ← he', he, add_sub_cancel_right]⟩
