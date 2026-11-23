import Formalism.SharpRestriction.InertJacobiLevels.ExtraF
import Formalism.SharpRestriction.InertJacobiLevels.AsmExtra
import Formalism.SharpRestriction.InertJacobiLevels.ExtraH
import Formalism.SharpRestriction.InertJacobiLevels.ExistsLatInst
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section RecF

variable (D1 : D7) (W : TwGap D1) (large₂ : LevGapD D1) (h0 : ∀ u, Module.finrank ℂ (D1.mem u).A.Mu0 = 0)
  (sc : Scale) (eOf : ℕ → ℕ)

def recF : D7 := recX D1 W large₂ h0 (rOfB (large₂.withTw W).recS sc) eOf (baseB (large₂.withTw W).recS)

def recF_gatT : GatTies (recF D1 W large₂ h0 sc eOf) :=
  recX_gatT D1 W large₂ h0 (rOfB (large₂.withTw W).recS sc) eOf (baseB (large₂.withTw W).recS)

def recF_more
    (hmt : ∀ w, (((D1.what₂.places.resChar w : ℕ) : ℝ) ≤ sc.X'' D1.R.n ∨
      D1.what₂.places.resChar w ∈ ({D1.host.d, D1.host.g 0, D1.host.g 1} : Finset ℕ)) ↔ D1.what₂.muAt w ≠ D1.what₂.mu0)
    (hA : ∀ j w, D1.what₂.Aj j w = 0) :
    RecMore (recF D1 W large₂ h0 sc eOf) (recF_gatT D1 W large₂ h0 sc eOf) sc where
  mu_tw := fun w hw L hL j _ _ =>
    fval_zero_of_tw (D := recF D1 W large₂ h0 sc eOf) (fun w => (hmt w).1) w hw L hL j
  Aj0 := fun w _ j _ _ => hA j w
  S0 := ∅
  mu_0 := fun w hw => ((hmt w).2 hw).elim Or.inl (fun h => Or.inr (Or.inl h))
  pos := fun _ X hbs hsc => posHypB (large₂.withTw W).recS h0 sc eOf X hbs hsc

def recF_ex (hS : ServedGap) (hGa : GaugeGap) (S : Shape0 D1)
    (hV : ∀ i j b k Q ψ, Subsingleton (W.nexp.MtV i j b k Q ψ)) (hF : ∀ i j b, Subsingleton (W.nexp.Fm i j b))
    (t : Ties (withTw D1 W)) (hb : Function.Bijective D1.embE) (hk : DV.KapDef D1)
    (hdu : ∀ u, ((D1.mem u).A.duStar : ℝ) = StandardLattice.duStarU D1 u) (hDs : D1.what₂.Dstar = StandardLattice.DstarD D1) :
    RecExtra (recF D1 W large₂ h0 sc eOf) eOf where
  shape := recX_shape D1 W large₂ h0 _ eOf _ S hV hF
  ties := recX_ties D1 W large₂ h0 _ eOf _ t
  X := recX_X D1 W large₂ h0 _ eOf _ S
  mjH := recX_mjH D1 W large₂ h0 _ eOf _ S
  kapR := rfl
  ep_tie := fun _ _ _ => rfl
  kap_def := hk
  duStar_def := hdu
  Dstar_def := hDs
  cover := W.cover
  le := recX_le D1 W large₂ h0 _ eOf _
  served := recX_served D1 W large₂ h0 _ eOf _ hS hb
  gauge := hGa _ _ _

end RecF

def PdeSplit {R : Ranks} (H : Host R) : Prop :=
  (Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E

def FdegAll : Prop := ∀ (R : Ranks) (h : HCParam R), FdegUniq R h

open Classical in

def twOf {R : Ranks} (H : Host R) (sc : Scale) : (@placesOf H.E _ _ H.cmStar).Pl → Bool :=
  fun w => decide ((((@placesOf H.E _ _ H.cmStar).resChar w : ℕ) : ℝ) ≤ sc.X'' R.n ∨
    (@placesOf H.E _ _ H.cmStar).resChar w ∈ ({H.d, H.g 0, H.g 1} : Finset ℕ))

theorem resCharW_conjW {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) :
    PlacesToy.resCharW (PlacesToy.conjW w) = PlacesToy.resCharW w :=
  PlacesToy.prime_mem_unique (PlacesToy.conjW w) (PlacesToy.resCharW_prime _) (PlacesToy.resCharW_prime w)
    (PlacesToy.resCharW_mem _) (by
      have h := (PlacesToy.mem_conjW_pow w ((PlacesToy.resCharW w : ℕ) : 𝓞 K) 1).2 (by
        rw [map_natCast, pow_one]; exact PlacesToy.resCharW_mem w)
      rwa [pow_one] at h)

theorem twOf_conj {R : Ranks} (H : Host R) (sc : Scale) (w) :
    twOf H sc ((@placesOf H.E _ _ H.cmStar).conj w) = twOf H sc w := by
  letI := H.cmStar
  unfold twOf
  have h : (placesOf H.E).resChar ((placesOf H.E).conj w) = (placesOf H.E).resChar w := resCharW_conjW w
  rw [h]

end Formalism.MainNotions.Inhab

end
