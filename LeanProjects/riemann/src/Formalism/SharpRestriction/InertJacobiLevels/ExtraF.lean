import Formalism.SharpRestriction.InertJacobiLevels.TrivialDatumMultiplicitySpaceSubsingleton
import Formalism.LocalRingCardinality.DataParams

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section

variable {R : Ranks} (H : Host R) (hc : Tau2 R → HCParam R) (etaF : ℝ) (Dn : ℕ) (hDel : (0 : ℚ) < (Dn : ℚ))
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * (Dn : ℚ))
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (hu : ∀ τ, FdegUniq R (hc τ))
  (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

def d7F : D7 := twistRecord H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw

theorem trivialFamily_shape_zero (hE : ∀ i, IsEmpty (K.cls (i + 1))) (hDG : K.DGam = minkM (2 * R.f * R.N R.m)) : Shape0 (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := shape_zero_trivialDatum H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw hE hDG

theorem trivialFamily_rank_zero (u) : Module.finrank ℂ ((d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.Mu0 = 0 := trivialDatum_finrank_zero H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw u

theorem trivialFamily_embedding_bijective : Function.Bijective (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).embE := Function.bijective_id

theorem trivialFamily_compatibilities (W : TwGap (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw)) : Ties (withTw (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) W) :=
  ties_withTw _ W rfl (fun τ V _ _ σ d h1 h2 => (hu τ).choose_spec.2 V σ d h1 h2)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) ⟨fun x => Empty.elim x⟩

theorem trivialFamily_dualStar_eq (h : (du : ℝ) = duStarH H hc) (u) :
    (((d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.duStar : ℝ) = StandardLattice.duStarU (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) u := h

theorem trivialFamily_discriminantStar_eq (hvl : vol = fun _ => volFor R H.g (fun τ => (hu τ).choose) Dst) :
    (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Dstar = StandardLattice.DstarD (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := by
  subst hvl
  exact dstar_def_of_vol _ rfl

theorem trivialFamily_kappaDef_congr (hv' : ℝ) (h : DV.KapDef (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw)) :
    DV.KapDef (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := h

theorem trivialFamily_exists_kappa : ∃ kb ks, DV.KapDef (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) :=
  twistRecord_weights_defined H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G tw htw

set_option maxHeartbeats 2000000 in
theorem trivialFamily_heightValue_eq (hv' : ℝ) (sc : Scale) (aT : H.TT → ℤ) (η Sc dl C : ℝ) (u) :
    hVal (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) sc aT η Sc dl C u = hVal (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) sc aT η Sc dl C u := rfl

theorem trivialFamily_logDerivative_eq (hv' : ℝ) (s : ℂ) :
    dlogL (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) s = dlogL (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) s := rfl

theorem trivialFamily_divisor_rank_zero : (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.R = 0 := by
  show ∑ u : Unit, (zeroHLat H.E).rank = 0
  simp [zeroHLat_rank]

end

end Formalism.MainNotions.Inhab

end
