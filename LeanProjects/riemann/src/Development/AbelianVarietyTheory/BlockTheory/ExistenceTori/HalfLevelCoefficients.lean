import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

structure IsHalf (D : D7) (Mb : Ideal (𝓞 D.host.E)) : Prop where
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {w0E D}}
  prod : Mb * Mb.map (bH D) = Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}
  coprime : Mb ⊔ Mb.map (bH D) = ⊤

theorem isHalf_levelG (D : D7) : IsHalf D (MbOf D [D.host.g 0, D.host.g 1]) where
  fromK := MbOf_fromK D _
  prod := by simpa [MbProdLaw] using MbProd_of D _ (splitG D)
  coprime := MbCop_of D _ (splitG D)

theorem three_le_g (D : D7) (k : Fin 2) : 3 ≤ D.host.g k := by
  have := (D.host.g_prime k).two_le
  have := g_ne_two D k
  omega

def levelAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Level (hostOfRecord D) where
  M := D.host.g 0 * D.host.g 1
  three_le := by
    have := three_le_g D 0
    have := three_le_g D 1
    nlinarith
  odd := ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  Mb := Mb
  fromK := h.fromK
  prod := h.prod
  coprime := h.coprime
  A := 1
  A_pos := Nat.one_pos

def coeffAt (D : D7) (hz : OZeta D) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Coeff (levelAt D Mb h) where
  F := FO D
  fin := inferInstance
  conj τ a := conj_mem_FO D τ a
  zeta_mem := by
    obtain ⟨y, hy⟩ := hz
    have : (levelAt D Mb h).M' = D.host.g 0 * D.host.g 1 := by
      simp [Level.M', levelAt]
    rw [this, ← hy]
    exact phiO_mem_FO D y
  le := by
    rw [KA, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨phi0_mem_coeff_field D D.host.sqrtMinusD, ?_⟩
    have : (levelAt D Mb h).A = 1 := rfl
    rw [this, zeta_one]
    exact one_mem _

open Classical in

def datAt (D : D7) (j : ℕ) : Datum (hostOfRecord D) :=
  if hj : InR D j then datumW D j hj else datumW D 1 (inR_one D)

theorem datAt_rank_pos (D : D7) (j : ℕ) : 1 ≤ (datAt D j).p + (datAt D j).q := by
  have := D.R.m_add_three_le_k
  unfold datAt
  split_ifs with hj
  · show 1 ≤ (D.R.sigW j).1 + (D.R.sigW j).2
    simp only [Ranks.sigW]
    have := hj.1
    omega
  · show 1 ≤ (D.R.sigW 1).1 + (D.R.sigW 1).2
    simp only [Ranks.sigW]
    omega

def parWith (D : D7) (hF : OFull D) (hz : OZeta D) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb)
    (Xo : ∀ j, Moduli (datAt D j) (levelAt D Mb h)) : Par D where
  H := hostOfRecord D
  l := levelAt D Mb h
  c := coeffAt D hz Mb h
  Dw := datAt D
  Xo := Xo
  eO := eOf D hF

def parAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Par D :=
  parWith D hF hz Mb h fun j =>
    Classical.choice (hN D.host.E (hostOfRecord D) (datAt D j) (levelAt D Mb h) (datAt_rank_pos D j))

def IsParAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (Q : Par D) : Prop :=
  Q.Pins ∧ Q.l.Mb = Mb ∧ ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q

def PrimesOver (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal

def halfOf (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Ideal (𝓞 D.host.E) :=
  ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def HalfOfPrimes (D : D7) : Prop :=
  ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), PrimesOver D pb → IsHalf D (halfOf D pb)

theorem halfOfPrimes_iff (D : D7) : HalfOfPrimes D ↔
    ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), PrimesOver D pb →
      ∃ l : Level (hostOfRecord D), l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1 ∧ l.Mb = halfOf D pb := by
  refine forall₂_congr fun pb _ => ⟨fun h => ⟨levelAt D _ h, rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨l, hM, -, hb⟩
  rw [← hb]
  exact ⟨l.fromK, hM ▸ l.prod, l.coprime⟩

theorem isParAt_parWith (D : D7) (hF : OFull D) (hz : OZeta D) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb)
    (Xo : ∀ j, Moduli (datAt D j) (levelAt D Mb h)) : IsParAt D Mb (parWith D hF hz Mb h Xo) := by
  refine ⟨⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, ⟨rfl, rfl⟩, eOf_spec D hF, fun j hj => ?_⟩, rfl, datAt_rank_pos D⟩
  show IsDatW D j (datAt D j)
  unfold datAt
  rw [dif_pos hj]
  unfold datumW datumOfRecord
  exact isDatW_datumOf D _ j _ _

theorem isParAt_parAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E))
    (h : IsHalf D Mb) : IsParAt D Mb (parAt D hF hz hN Mb h) :=
  isParAt_parWith D hF hz Mb h _

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients
