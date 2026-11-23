import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def xplusProv (X : Prov D B P) (E : ∀ j h1 h2, PtExt (X j h1 h2))
    (hM : ∀ j h1 h2, IntAtExt (X j h1 h2) (E j h1 h2)) : Prov D B P :=
  fun j h1 h2 => xplus (X j h1 h2) (E j h1 h2) (hM j h1 h2)

section Up

variable {j : ℕ} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) {ka wL wF : WeightFamilies.Wt D j}

theorem hypC_xplus (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    HypC large₂ (xplus X E hM) H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus ↔
      HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := Iff.rfl

theorem deepSubMul_xplus : DeepSubMul (xplus X E hM) ↔ DeepSubMul X := Iff.rfl

variable {X} (G : GlobalFamilyData X ka wL wF)

theorem tiedW_up (S : Scal B) (Gc Prw : ℝ) : (gd2Xplus G E hM).TiedW S Gc Prw ↔ G.TiedW S Gc Prw := Iff.rfl

theorem tiedTh_up (S : Scal B) (Gc : ℝ) : (gd2Xplus G E hM).TiedTh S Gc ↔ G.TiedTh S Gc := Iff.rfl

theorem tiedEt_up (large₂ : SizeData₂ D) (Cf Af : ℝ) : (gd2Xplus G E hM).TiedEt large₂ Cf Af ↔ G.TiedEt large₂ Cf Af := Iff.rfl

theorem inBasis_up (la : HeightOneSpectrum (𝓞 B.KO)) : InBasis (gd2Xplus G E hM) la ↔ InBasis G la := Iff.rfl

end Up

section N

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (n0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (n1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (n2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (n3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (n4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

def xplusProvN (X : Prov D B P) (E : ∀ j h1 h2, PtExt (X j h1 h2))
    (hM : ∀ j h1 h2, IntAtExt (X j h1 h2) (E j h1 h2)) : Prov D (withNorm B N n0 n1 n2 n3 n4) P :=
  fun j h1 h2 => xplusN N n0 n1 n2 n3 n4 (X j h1 h2) (E j h1 h2) (hM j h1 h2)

section UpN

variable {j : ℕ} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) {ka wL wF : WeightFamilies.Wt D j}

theorem latAt_N : LatAt (withNorm B N n0 n1 n2 n3 n4) j ka ↔ LatAt B j ka := Iff.rfl

theorem lamwAt_N (large₂ : SizeData₂ D) (C A : ℝ) : LAMwAt large₂ (withNorm B N n0 n1 n2 n3 n4) j ka C A ↔ LAMwAt large₂ B j ka C A :=
  Iff.rfl

set_option maxHeartbeats 4000000 in
theorem qAt_N (large₂ : SizeData₂ D) (CR Ck Ch Ah Cc Ac T c : ℝ) :
    QAt large₂ (withNorm B N n0 n1 n2 n3 n4) j ka CR Ck Ch Ah Cc Ac T c ↔ QAt large₂ B j ka CR Ck Ch Ah Cc Ac T c := Iff.rfl

variable {X} (G : GlobalFamilyData X ka wL wF)

end UpN

end N

end Formalism.L2.Pj
