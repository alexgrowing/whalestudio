import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitQuotientPrimePowEqExponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeQuotientLeCocycleSpanDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCoboundariesAmongBlockCocyclesLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActDEqOfEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthEqInfKerAddMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocyclesCharBlockOtherTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeShaStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexDvdClassNumber
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CutCore

theorem length_mono {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {A B : Submodule O M} (h : A ≤ B) :
    Module.length O ↥A ≤ Module.length O ↥B :=
  Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem exists_length_quot {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} (ha : a ≠ 0) :
    ∃ n : ℕ, Module.length O (O ⧸ Ideal.span {a}) = n := by
  have h : Ring.ord O a ≠ ⊤ := by
    rwa [Ring.ord_eq_addVal, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp h
  exact ⟨e, he.symm⟩

theorem length_quot_eq_zero_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} :
    Module.length O (O ⧸ Ideal.span {a}) = 0 ↔ IsUnit a := by
  change Ring.ord O a = 0 ↔ _
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_eq_zero_iff]

variable {D : D7} (i : D.nd.Loc)

theorem resIne_eq_bot_of_le {k : ℕ} {A B : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)} (h : A ≤ B)
    {v : HeightOneSpectrum (𝓞 D.host.E)} (hB : resIne i B v = ⊥) : resIne i A v = ⊥ :=
  le_bot_iff.mp (hB ▸ Submodule.map_mono h)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lenCob_mono {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    {A B : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)} (h : A ≤ B) : lenCob i M A ≤ lenCob i M B :=
  length_mono (inf_le_inf_right _ h)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i))
  (S : IdempotentChoiceData D.nd i)

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => S.T'.one_mem, by
    funext x'
    simp⟩

theorem del_ne_zero (hS : GoodCongruenceObjects D.nd r ρ π S) : del51 D.nd S S.π' ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨h1, -, h3, -⟩, -⟩ := hS
  intro h0
  have hz : (Eel D.nd S S.π').map (toK D.nd i) = 0 := by
    rw [← Matrix.toLin'.map_eq_zero_iff]
    refine LinearMap.ext fun u => ?_
    apply S.e.injective
    rw [Matrix.toLin'_apply, h3 u, h0]
    simp [Prod.ext_iff, funext_iff]
  have := h1 S.π'
  rw [hz, Matrix.rank_zero] at this
  exact zero_ne_one this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem length_cocRho_le (eρ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs (WpO D.nd i ρ π) eρ) :
    Module.length (D.nd.O i) ↥(cocRho i r S Xs) ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * eρ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
        (((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') +
          Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π)) := by
  obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Xs _ (WpO D.nd i ρ π) (cocRho i r S Xs) eρ
    (fun w hw => ⟨hL w hw, (GlobalTheory.T.localised_global_cocycles_in_local_span D i r ρ π Xs S hr hS hπ w hw).1⟩)
  refine hlen.trans (add_le_add le_rfl ?_)
  refine (GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).1) hfin ?_).trans
    (add_le_add ((lenCob_mono i _ hC).trans (GlobalTheory.T.length_coboundaries_among_block_cocycles_le D i r ρ π Xs S hr hS hπ).1) le_rfl)
  intro v h1 h2 h3
  exact resIne_eq_bot_of_le i hC
    (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Xs S _ S.ψρ (inR'_one i r S) hU v h1 h2 h3)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_fin_unr (eχ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hSv : ∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v)
    (hQ : ∀ v ∈ D.nd.Q i, QuadAt i r Xs v) (c : Fin D.R.t)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      LocBound i w hw r Xs (chiRatO D.nd i ((c : ℕ) + 1)) eχ) :
    ∃ C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1), C ≤ cocChi i r S Xs c ∧
      (∀ f ∈ C, IsFinL i (chiRatO D.nd i ((c : ℕ) + 1)) f) ∧
      (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C v = ⊥) ∧
      Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
        (((placesOver D.host.E (D.nd.l i)).ncard * eχ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
          (Module.length (D.nd.O i) ↥C + ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1)) := by
  obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Xs _ (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) eχ
    (fun w hw => ⟨hL w hw, (GlobalTheory.T.localised_global_cocycles_in_local_span D i r ρ π Xs S hr hS hπ w hw).2 c⟩)
  obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 C (D.nd.Q i)
  refine ⟨C', hC'.trans hC, fun f hf => hfin f (hC' hf), ?_, hlen.trans (add_le_add le_rfl
    (hlen'.trans (add_le_add le_rfl (Finset.sum_le_sum fun q hq' => ?_))))⟩
  · intro v h1
    by_cases h3 : v ∈ D.nd.Q i
    · exact hq v h3
    refine resIne_eq_bot_of_le i (hC'.trans hC) ?_
    by_cases h2 : v ∈ D.nd.S i
    · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
      · have h := GlobalTheory.T.length_inertia_restriction_cocycles_le D i r ρ π Xs S hr hS hπ v (Or.inl h2) hqd c
        rw [lenQ, length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
        exact Submodule.subsingleton_iff_eq_bot.mp h
      · exact GlobalTheory.T.inertiaCocycles_charBlock_otherTypePrime D i r ρ π Xs S hr hS hπ v h2 hp c
    · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Xs S _ _ (inR'_one i r S) hU v h1 h2 h3
  · exact (length_mono (Submodule.map_mono hC)).trans
      (GlobalTheory.T.length_inertia_restriction_cocycles_le D i r ρ π Xs S hr hS hπ q (Or.inr hq') (hQ q hq') c)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem length_cocChi_le (hA : GlobalTheory.Published.GlobalArtinReciprocity) (eχ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hSv : ∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v)
    (hQ : ∀ v ∈ D.nd.Q i, QuadAt i r Xs v) (c : Fin D.R.t)
    (hH : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      LocBound i w hw r Xs (chiRatO D.nd i ((c : ℕ) + 1)) eχ) :
    Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * eχ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
        ((2 * lenQ i (del51 D.nd S S.π') + lenQ i ((D.nd.l i : ℕ) : D.nd.O i) *
            (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
              else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ))) +
          ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1)) := by
  obtain ⟨C, hC, hfin, hunr, hlen⟩ := exists_fin_unr i r ρ π Xs S eχ hr hS hπ hU hSv hQ c hL
  refine hlen.trans (add_le_add le_rfl (add_le_add ?_ le_rfl))
  have hZ := hC.trans ((GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c)
  by_cases hc : (c : ℕ) = 0
  · rw [if_pos hc]
    rw [hc, zero_add] at hZ hfin
    refine (GlobalTheory.UnramHom.length_le_classNumber hA D i C hZ fun v => ?_).trans le_add_self
    by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
    · exact GlobalTheory.CutTrivIne.main D i C v hv fun f hf => (hH v hv).2 (hfin f hf v hv)
    · exact hunr v hv
  · rw [if_neg hc]
    have h2 : 2 ≤ (c : ℕ) + 1 := by omega
    have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
    have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C hZ h2 ht
      (fun f hf w hw => (hH w hw).1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) (hfin f hf w hw)) hunr
    rw [Nat.add_sub_cancel] at h
    exact h.trans (add_le_add ((lenCob_mono i _ hC).trans
      ((GlobalTheory.T.length_coboundaries_among_block_cocycles_le D i r ρ π Xs S hr hS hπ).2 c)) le_rfl)

theorem sum_fin_ite {t : ℕ} (ht : 0 < t) (h : ℕ) (g : ℕ → ℕ) :
    ∑ c : Fin t, (if (c : ℕ) = 0 then h else g c) = h + ∑ e ∈ Finset.Ioo 0 t, g e := by
  rw [Fin.sum_univ_eq_sum_range (fun c => if c = 0 then h else g c) t]
  have : Finset.range t = insert 0 (Finset.Ioo 0 t) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [this, Finset.sum_insert (by simp), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun e he => if_neg (Finset.mem_Ioo.mp he).1.ne'

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalCore := by
  intro hA D i r ρ π Xs eρ eχ S hr hS hZ hπ hN hU hSv hQ hl hsel hsha
  classical
  obtain ⟨L, hL⟩ := exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (length_quot_eq_zero_iff.mp hL)
  obtain ⟨d, hd⟩ := exists_length_quot (del_ne_zero i r ρ π S hS)
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)
  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set n := (placesOver D.host.E (D.nd.l i)).ncard with hn
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hρ := length_cocRho_le i r ρ π Xs S eρ hr hS hπ hU fun w hw => (hl w hw).2.1
  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
      ((n * eχ * L + ((2 * d + L * (if (c : ℕ) = 0 then h else g c)) + ∑ q ∈ D.nd.Q i, z q) : ℕ) : ℕ∞) := by
    intro c
    refine (length_cocChi_le i r ρ π Xs S hA eχ hr hS hπ hU hSv (fun v hv => (hQ v hv).1) c
      (fun w hw => (hl w hw).1) fun w hw => (hl w hw).2.2 _
        (Finset.mem_Icc.mpr ⟨Nat.le_add_left _ _, c.2⟩)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, lenQ, hL, hd]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  rw [lenQ, lenQ, hL, hd, ← hs] at hρ
  have htot := (GlobalTheory.T.length_heckeQuotient_le_cocycleSpan_determinant D i r ρ π Xs S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ c))
  rw [← Nat.cast_sum, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, sum_fin_ite ht] at hnat
  have hvd : D.nd.vdel i = (d : ℚ) / L := by
    rw [← hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2, lenUnit, hL, hd, ENat.toNat_coe, ENat.toNat_coe]
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  rw [hvd, hsp, hsh, hzq, vccOff, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat
  have hq : (a : ℚ) ≤ _ := Nat.cast_le.mpr hnat
  rw [div_le_iff₀ hLq, Ranks.nV]
  push_cast at hq ⊢
  have hd0 : (0 : ℚ) ≤ ((D.R.r : ℚ) + D.R.t) * d := by positivity
  field_simp
  nlinarith [hq, hd0]

end GlobalTheory.CutCore
