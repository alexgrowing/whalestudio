import Formalism.SharpRestriction.InertJacobiLevels.ExtraRec
import Formalism.LocalRingCardinality.SpanPowerMembership.TwistRecordRowDimensionZero

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

variable {R : Ranks} (H : Host R)

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
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

theorem trivialDatum_multiplicity_subsingleton : ∀ μ j, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Mult μ j) :=
  fun _ _ => inferInstanceAs (Subsingleton Z0)

theorem trivialDatum_ambient_subsingleton : ∀ μ, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Amb μ) :=
  fun _ => inferInstanceAs (Subsingleton Z0)

theorem trivialDatum_metricLattice_subsingleton : ∀ μ j, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.MtL μ j) :=
  fun _ _ => inferInstanceAs (Subsingleton PUnit)

theorem trivialDatum_multiplicity_space_subsingleton : ∀ j, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Mj j) :=
  fun _ => inferInstanceAs (Subsingleton Z0)

theorem trivialDatum_error_space_subsingleton : Subsingleton (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.EE0 :=
  inferInstanceAs (Subsingleton Z0)

theorem trivialDatum_radical_subsingleton : Subsingleton (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.RR.V :=
  inferInstanceAs (Subsingleton (zeroHLat H.E).V)

theorem trivialDatum_nu_subsingleton : ∀ u, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.Nu u).V :=
  fun _ => inferInstanceAs (Subsingleton (zeroHLat H.E).V)

theorem trivialDatum_lattice_subsingleton : ∀ u j, Subsingleton (((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).fm u).lat j).V :=
  fun _ _ => inferInstanceAs (Subsingleton (fmZeroHLat H.E).V)

theorem trivialDatum_twisted_points_isEmpty : ∀ u μ i, IsEmpty (((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).chTw u μ).Y i) :=
  fun _ _ _ => ⟨fun y => Empty.elim y⟩

theorem trivialDatum_metricVector_subsingleton : ∀ i j b k Q ψ, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).nexp.MtV i j b k Q ψ) :=
  fun i => Empty.elim i

theorem trivialDatum_forms_subsingleton : ∀ i j b, Subsingleton ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).nexp.Fm i j b) :=
  fun i => Empty.elim i

theorem trivialDatum_mem_base_lattice : ∀ x : (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.LL, x ∈ (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).LL0 :=
  fun _ => trivial

theorem trivialDatum_gammaDiscriminant_eq : ∀ u μ, ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).chTw u μ).DGam = ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).u₀).C.DGam :=
  fun _ _ => rfl

theorem trivialDatum_class_zero_equiv : ∀ u μ, Nonempty (((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).C.cls 0 ≃ ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).chTw u μ).cls 0) :=
  fun _ _ => ⟨Equiv.refl _⟩

theorem trivialDatum_twisted_classes_isEmpty (hE : ∀ i, IsEmpty (K.cls (i + 1))) : ∀ u μ j, IsEmpty (((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).chTw u μ).cls (j + 1)) :=
  fun _ _ j => hE j

theorem trivialDatum_isEmpty_local : IsEmpty (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).nd.Loc := ⟨fun a => Empty.elim a⟩

theorem shape_zero_trivialDatum (hE : ∀ i, IsEmpty (K.cls (i + 1))) (hDG : K.DGam = minkM (2 * R.f * R.N R.m)) : Shape0 (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) where
  mult := trivialDatum_multiplicity_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  amb := trivialDatum_ambient_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  mtL := trivialDatum_metricLattice_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  mj := trivialDatum_multiplicity_space_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  ee0 := trivialDatum_error_space_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  rr := trivialDatum_radical_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  nu := trivialDatum_nu_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  lat := trivialDatum_lattice_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  yTw := trivialDatum_twisted_points_isEmpty H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  clsTw := trivialDatum_twisted_classes_isEmpty H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw hE
  mtV := trivialDatum_metricVector_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  fmN := trivialDatum_forms_subsingleton H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  ll0 := trivialDatum_mem_base_lattice H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  Ij0 := fun _ _ _ => rfl
  jw0 := fun _ _ _ => rfl
  drows := rfl
  dgam := trivialDatum_gammaDiscriminant_eq H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  mink := hDG
  loc := trivialDatum_isEmpty_local H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw
  cls0 := trivialDatum_class_zero_equiv H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw

theorem trivialDatum_finrank_zero (u) : Module.finrank ℂ ((twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.Mu0 = 0 := by
  show Module.finrank ℂ (⊥ : Submodule ℂ (K.cls 0 → Empty → ℂ)) = 0
  exact finrank_bot ℂ _

theorem trivialDatum_embedding_bijective : Function.Bijective (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).embE := Function.bijective_id

def dstFor (R : Ranks) (du : ℕ) (Ts Gam : ℝ) : ℝ := (du : ℝ) * dstarOfRanks R Ts Gam

theorem dstFor_pos (R : Ranks) {du : ℕ} (hdu : 0 < du) {Ts Gam : ℝ} (hTs : 0 < Ts) (hG : 1 < Gam) :
    0 < dstFor R du Ts Gam := mul_pos (by exact_mod_cast hdu) (dstar2_pos R hTs hG)

omit hT in
theorem tstar_dstFor (R : Ranks) {du : ℕ} (hdu : 0 < du) {Ts Gam : ℝ} (hTs : 0 < Ts) (hG : 1 < Gam) :
    (dstFor R du Ts Gam / du) ^ ((1 : ℝ) / (R.f * R.k)) * Gam ^ (-(2 : ℝ) / (R.f * R.k)) = Ts := by
  have hG0 : 0 < Gam := by linarith
  have hd : ((du : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdu.ne'
  have hn : (R.f : ℝ) * (R.k : ℝ) = ((R.f * R.k : ℕ) : ℝ) := by push_cast; ring
  unfold dstFor
  rw [mul_div_cancel_left₀ _ hd, hn, one_div, dstarOfRanks,
    Real.pow_rpow_inv_natCast (by positivity) (fk_ne R), mul_assoc, ← Real.rpow_add hG0]
  rw [show (2 : ℝ) / ((R.f * R.k : ℕ) : ℝ) + -2 / ((R.f * R.k : ℕ) : ℝ) = 0 by ring, Real.rpow_zero,
    mul_one]

def LevGap : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) [Fact T.Prime] (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}),
    (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)) →
    ∃ (K : ClsPkg) (_ : ∀ i, IsEmpty (K.cls (i + 1))) (_ : K.DGam = minkM (2 * R.f * R.N R.m))
      (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
      (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c)),
      ∀ hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin hg ht G kb ks tw htw,
        Nonempty (LevGapD (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw))

end Formalism.MainNotions.Inhab

end
