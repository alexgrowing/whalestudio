import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslA
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCoefficientsCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystemStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.UPel.HT.HeckeAd

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

theorem exists_isTranslA : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), 3 ≤ N → N.Coprime p → c.Coprime p → k.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsTranslA (h (N * k)) c k N o o' ψ := by
  intro p _ D R _ b h u c k N hN hNp hc hk hck hlin hcomp hsim honto S _ s o
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact (Fact.out : p.Prime).one_lt.ne' hk)
  have hN0 : 0 < N := by omega
  have hNk : 0 < N * k := Nat.mul_pos hN0 hk0
  have hNkp : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  set f := h (N * k) with hf
  obtain ⟨hfin, hfree⟩ := GlobalTheory.UPel.HT.HeckeAd.heckeSubA_finite_free b f k N hk0 hN0 hk hNp s o
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.TranslQuotient.exists_quotient S o.A
    (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) o.ab (pull_isLB o.isLB _)
    o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N, g ≫ ψ = 1 := fun g hg =>
    GlobalTheory.UPel.HT.Hecke.comp_eq_one_of_transl ψ g (hgal.inv ⟨g, hg⟩)
  have stab : ∀ c' : D.O, ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N,
      g ≫ o.act.act c' ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N := fun c' g hg =>
    GlobalTheory.UPel.HT.HeckeAd.act_mem o f (hlin (N * k) hNk hNkp) c' g hg
  choose actf hactf using fun c' : D.O => GlobalTheory.UPel.HT.Hecke.exists_desc_endo S o.A A'
    (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp' : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm

  have hker := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hck hlin hcomp hsim honto S s o
  obtain ⟨u₀, hu₀, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ (k ^ 2 / c)
    (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) (fun g hg => (hker g hg).1) (fun g hg => (hker g hg).2)
    (GlobalTheory.T.heckeSections_isotropic_commutatorPairing_power p D R b h u c k N hc hk hN hNp hck hlin hcomp hsim honto S s o)
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) ψ hψ hgal
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (GlobalTheory.UPel.HT.Hecke.sq2 ψ) _ _
    (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) hGC (DVR.linComb_isLB _ o.isLB _ _) u₀ hu₀ hcoc
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b (N * k) S s o A' ψ hψ _ P₀ hP₀ w₀
  have hk2 : 0 < k ^ 2 := by positivity
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hck; omega)
  have hm1 : 1 ≤ k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd hk2 hck) hc0
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (hk.pow_left 2)
  have hsym := GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b (N * k) S s o A' ψ _ hA' hψ hgal _ P' hP' w r1 r2
  have hamp := GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b (N * k) S s o A' ψ _ hA' hψ hgal _ hm1 P' hP' w
  have hkerP := GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p p D R b (N * k) S s o A' ψ _ hA' hψ hgal _ hmp P' hP' w
  have hros := GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b (N * k) S s o A' act' ψ _ hA' hψ hgal hcomp' _ P' hP' w r1 r2
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.UPel.HT.EtaleLie.lie_of_etale p D R b (N * k) S s o A' act' ψ _ _ hA' hψ hgal hcomp'
  have hgeom := GlobalTheory.T.exists_tateSimilitude_heckeTranslate_latticeSystem p D R b h u c k N hc hk hN hNp hck hlin hcomp hsim honto S s o A' act' ψ hA' hψ hgal
    hcomp' P' hP' r1 r2 w
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hkerP
      rosati := hros
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta (f x) ≫ ψ
      eta_add := fun x y => by rw [map_add, o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (f (c' • x)) ≫ ψ = (o.eta (f x) ≫ ψ) ≫ act'.act c'
        obtain ⟨z, hz⟩ := hlin (N * k) hNk hNkp c' x
        rw [← hf] at hz
        rw [hz, o.eta_add, o.eta_ker, _root_.mul_one, o.eta_lin, Category.assoc, hcomp', Category.assoc]
      eta_ker := fun x => by rw [map_nsmul]; exact kill _ (GlobalTheory.UPel.HT.HeckeAd.mem_heckeSubA o f N x)
      geom := hgeom }
  exact ⟨o', ψ, hψ, hcomp', fun x => rfl, hgal, ⟨w⟩, hck⟩

end GlobalTheory.UPel.HT.HeckeAd
