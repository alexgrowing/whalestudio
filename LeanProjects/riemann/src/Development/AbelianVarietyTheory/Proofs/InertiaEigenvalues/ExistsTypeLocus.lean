import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePartitionsPermStatement
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Polynomial

namespace GlobalTheory.CutAtGood

section AtPlace

attribute [local instance] Formalism.BasicNotions.Examples₂.NZ.neZero_g Formalism.BasicNotions.Examples₂.NZ.fact_g Classical.propDecidable

variable (D : D7)

theorem atPlace_add (k : Fin 2) (v : D.nd.PlG k) (a b : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (a + b) = Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a + Formalism.MainNotions.ArithmeticCylinders.atPlace D k v b := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  rw [MonoidAlgebra.coeff_add, Finsupp.mapDomain_add, MonoidAlgebra.ofCoeff_add]

theorem atPlace_zero (k : Fin 2) (v : D.nd.PlG k) : Formalism.MainNotions.ArithmeticCylinders.atPlace D k v 0 = 0 := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  rw [MonoidAlgebra.coeff_zero, Finsupp.mapDomain_zero, MonoidAlgebra.ofCoeff_zero]

theorem atPlace_sum (k : Fin 2) (v : D.nd.PlG k) {ι : Type} (S : Finset ι)
    (a : ι → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (∑ i ∈ S, a i) = ∑ i ∈ S, Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, atPlace_zero]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, atPlace_add, ih]

theorem atPlace_eq_tens (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a = Formalism.BasicNotions.Examples₂.NZ.tens
      (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      (Function.update (fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
        (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))))) ⟨k, v⟩ a) := by
  classical
  have hinj : Function.Injective (Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
      GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k)) := by
    intro x y h
    have := congrFun h ⟨k, v⟩
    rwa [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same] at this
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [Formalism.BasicNotions.Examples₂.NZ.tens_coeff]
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  rw [MonoidAlgebra.coeff_ofCoeff]
  by_cases hg : g ∈ Set.range (Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
      GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k))
  · obtain ⟨h, rfl⟩ := hg
    rw [Finsupp.mapDomain_apply hinj, Fintype.prod_eq_single (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k)
      (fun i hi => by rw [Function.update_of_ne hi, Pi.mulSingle_eq_of_ne hi, MonoidAlgebra.coeff_one_one]),
      Function.update_self, Pi.mulSingle_eq_same]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hg]
    have hex : ∃ i, i ≠ (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) ∧ g i ≠ 1 := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      apply hg
      refine ⟨g ⟨k, v⟩, funext fun i => ?_⟩
      by_cases hi : i = ⟨k, v⟩
      · subst hi
        rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, hc i hi]
    obtain ⟨i, hi, hgi⟩ := hex
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [Function.update_of_ne hi, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg (Ne.symm hgi)]

theorem atPlace_one (k : Fin 2) (v : D.nd.PlG k) : Formalism.MainNotions.ArithmeticCylinders.atPlace D k v 1 = 1 := by
  classical
  have hu : Function.update (fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
      (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))))) ⟨k, v⟩ 1 = fun _ => 1 :=
    Function.update_eq_self_iff.mpr rfl
  rw [atPlace_eq_tens, hu]
  exact Formalism.BasicNotions.Examples₂.NZ.tens_single (k := ℂ) 1

theorem atPlace_mem_center (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (ha : ∀ b, a * b = b * a) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
  classical
  rw [Subalgebra.mem_center_iff, atPlace_eq_tens]
  intro b
  refine (Formalism.BasicNotions.Examples₂.NZ.tens_central _ (fun i c => ?_) b).symm
  rcases eq_or_ne i ⟨k, v⟩ with rfl | hi
  · rw [Function.update_self]
    exact ha c
  · rw [Function.update_of_ne hi, one_mul, mul_one]

end AtPlace

section OnMt

variable (D : D7) (μ : D.what₂.Tup) (j : ℕ)

local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))

theorem onMt_mul {a b : MonoidAlgebra ℂ (G0g D.nd)} (ha : a ∈ CZ) (hb : b ∈ CZ) :
    D.ntypes.onMt μ j (a * b) = D.ntypes.onMt μ j a * D.ntypes.onMt μ j b := by
  unfold NTypes.onMt
  rw [dif_pos (Subalgebra.mul_mem _ ha hb), dif_pos ha, dif_pos hb]
  have e : (⟨a * b, Subalgebra.mul_mem _ ha hb⟩ : ↥CZ) = ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
  rw [e, map_mul]

theorem onMt_add {a b : MonoidAlgebra ℂ (G0g D.nd)} (ha : a ∈ CZ) (hb : b ∈ CZ) :
    D.ntypes.onMt μ j (a + b) = D.ntypes.onMt μ j a + D.ntypes.onMt μ j b := by
  unfold NTypes.onMt
  rw [dif_pos (Subalgebra.add_mem _ ha hb), dif_pos ha, dif_pos hb]
  exact map_add (D.ntypes.cenMt μ j) ⟨a, ha⟩ ⟨b, hb⟩

theorem onMt_one : D.ntypes.onMt μ j 1 = 1 := by
  unfold NTypes.onMt
  rw [dif_pos (Subalgebra.one_mem _)]
  exact map_one (D.ntypes.cenMt μ j)

theorem onMt_smul (c : ℂ) {a : MonoidAlgebra ℂ (G0g D.nd)} (ha : a ∈ CZ) :
    D.ntypes.onMt μ j (c • a) = c • D.ntypes.onMt μ j a := by
  unfold NTypes.onMt
  rw [dif_pos (Subalgebra.smul_mem _ ha c), dif_pos ha]
  exact map_smul (D.ntypes.cenMt μ j) c ⟨a, ha⟩

theorem onMt_sum {ι : Type} (S : Finset ι) (a : ι → MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ i ∈ S, a i ∈ CZ) :
    D.ntypes.onMt μ j (∑ i ∈ S, a i) = ∑ i ∈ S, D.ntypes.onMt μ j (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    unfold NTypes.onMt
    rw [Finset.sum_empty, Finset.sum_empty, dif_pos (Subalgebra.zero_mem _)]
    exact map_zero (D.ntypes.cenMt μ j)
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      onMt_add D μ j (ha i (Finset.mem_insert_self i S))
        (Subalgebra.sum_mem _ fun x hx => ha x (Finset.mem_insert_of_mem hx)),
      ih fun x hx => ha x (Finset.mem_insert_of_mem hx)]

theorem onMt_prod (L : List (MonoidAlgebra ℂ (G0g D.nd))) (hL : ∀ a ∈ L, a ∈ CZ) :
    D.ntypes.onMt μ j L.prod = (L.map (D.ntypes.onMt μ j)).prod ∧ L.prod ∈ CZ := by
  induction L with
  | nil => exact ⟨onMt_one D μ j, Subalgebra.one_mem _⟩
  | cons a L ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => hL b (List.mem_cons_of_mem a hb)
    have ha := hL a List.mem_cons_self
    rw [List.prod_cons, List.map_cons, List.prod_cons, onMt_mul D μ j ha h2, h1]
    exact ⟨rfl, Subalgebra.mul_mem _ ha h2⟩

end OnMt

section Record

variable {D : D7}

theorem isoLoc_perm {Pa Pb : List (Part D.naut.CG)} (h : Pa.Perm Pb) (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pb w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [List.foldr_cons, ih]
  | swap p q l =>
    simp only [List.foldr_cons]
    rw [← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc D.nd D.naut q w), D.naut.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem locG_tw_back (hL : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    D.naut.locG (D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv) w = D.naut.locG π w := by
  obtain ⟨h1, h2⟩ := D.naut.etaTinv_def w
  have d1 := D.naut.locG_dim D.naut.etaTinv w
  have d2 := D.naut.locG_dim D.naut.etaT w
  have hu2 := D.naut.etaT_unr w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu2).trans d2)
  have hc0 : c ≠ 0 := by
    have := D.naut.frobEig_ne_zero _ hu2
    rw [hc] at this
    simpa [eq_comm] using this
  have hc' : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
    rw [h2, hc, Multiset.map_singleton]
  have hu := D.naut.unr_char _ _ d1 hu2 h1
  have hf : D.naut.frobEig (D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w)) = {1} := by
    rw [D.naut.frobEig_char _ _ c⁻¹ hu2 h1 d1 hc', hc]
    simp [hc0]
  have he : D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
    rw [D.naut.unr_eq_lpUnr _ hu, hf]
  obtain ⟨-, -, -, e1, e2, -⟩ := hL w (D.naut.locG π w) (D.naut.locG π w) (D.naut.locG D.naut.etaT w)
    (D.naut.locG D.naut.etaTinv w) 0 d2 d1
  rw [D.naut.locG_tw, D.naut.locG_tw, e1, he, e2]

theorem isBCV_perm {i : D.nd.Loc} {P : D.naut.AV i} {Pa Pa' : List (Part D.naut.CG)}
    (h : IsBCV D.nd D.naut i P Pa) (hp : Pa.Perm Pa') : IsBCV D.nd D.naut i P Pa' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun p hp' => h1 p (hp.mem_iff.2 hp'), (hp.map _).nodup_iff.1 h2, ?_, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_⟩
  · unfold rankIso at h3 ⊢
    rw [← (hp.map _).sum_eq]
    exact h3
  · rw [← isoLoc_perm hp w]
    exact h4 w hw
  · rw [← isoLoc_perm hp w]
    exact h5 w hw
  · unfold isoInf at h6 ⊢
    rw [← (hp.map _).sum_eq]
    exact h6 τ

theorem bc_all (hT0 : SumRepresentations.tie0 D) (hG : SumRepresentations.adm2 D) (h5 : SumRepresentations.adm5 D) (hBC : SumRepresentations.adm1 D) {i : D.nd.Loc}
    {x : D.nd.X i} {P0 PI : D.naut.AV i} (h0 : D.naut.ptV i P0 = some x) (hx : D.naut.ptV i PI = some x)
    {Pa0 : List (Part D.naut.CG)} (hB0 : IsBCV D.nd D.naut i P0 Pa0) : IsBCV D.nd D.naut i PI Pa0 := by
  obtain ⟨Pa, hPa⟩ := hBC i PI
  have hp := GlobalTheory.T.base_change_partitions_perm D hT0 hG h5 i x P0 PI Pa0 Pa h0 hx hB0 hPa
  exact isBCV_perm hPa hp.symm

theorem typeV_le_mtPar {i : D.nd.Loc} {PI : D.naut.AV i} {Sig : List (Part D.naut.CG)} {σ' : D.ntypes.Par}
    (hσ : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w)
    (hB : IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)) :
    D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
  rw [D.mtpar_tie i σ']
  exact le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl

theorem tw_tw (hT0 : SumRepresentations.tie0 D) (h5 : SumRepresentations.adm5 D) {a : ℕ} (π : D.naut.CG a) (ha : 1 ≤ a) :
    D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π := by
  have hloc : ∀ w, D.naut.locG (D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv) w = D.naut.locG π w :=
    fun w => locG_tw_back hT0.1 π w
  have hp := h5.1 [⟨a, D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      simp only [isoLoc, spehLoc, List.foldr_cons, List.foldr_nil, hloc])
  have hpp := List.singleton_perm_singleton.1 hp
  exact eq_of_heq (Formalism.BasicNotions.Part.mk.inj hpp).2.1

theorem hasParamX_of_Z (hT0 : SumRepresentations.tie0 D) (h5 : SumRepresentations.adm5 D) {i : D.nd.Loc} {x : D.nd.X i}
    (hx : x ∈ D.nd.Z i) : ∃ Sig, HasParamX D.nd D.naut i x Sig := by
  classical
  obtain ⟨P1, hP1, Pa, hB, hm⟩ := (D.Z_tie i x).1 hx
  refine ⟨twistIso D.nd D.naut (Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩) D.naut.etaT,
    P1, hP1, isBCV_perm hB ?_⟩
  have hid : ∀ p ∈ Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩,
      (⟨p.a, D.naut.tw (D.naut.tw p.π D.naut.etaT) D.naut.etaTinv, p.d⟩ : Part D.naut.CG) = p := by
    intro p hp
    have hpa := (hB.1 p (List.mem_of_mem_erase hp)).1
    obtain ⟨pa, pπ, pd⟩ := p
    simp only [tw_tw hT0 h5 pπ hpa]
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩)
      D.naut.etaT ++ [muPart D.nd D.naut i]) D.naut.etaTinv =
      Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ ++
        [⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩] := by
    unfold twistIso muPart
    rw [List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) ?_ rfl
    calc _ = List.map id (Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩) :=
          List.map_congr_left fun p hp => hid p hp
      _ = _ := List.map_id _
  rw [e]
  exact (List.perm_cons_erase hm).trans (List.perm_append_singleton _ _).symm

theorem labPar_eq {σ' : D.ntypes.Par} {Sig : List (Part D.naut.CG)}
    (hσ : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) (k : Fin 2) (v : D.nd.PlG k) :
    D.ntypes.labPar k σ' v = D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
  rw [D.ntypes.labPar_def, hσ]

theorem goodSig_of_labels {Sig Sig' : List (Part D.naut.CG)}
    (h : ∀ k v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig' (D.naut.plGw k v)))
    (hg : goodSig D.nd D.naut Sig) : goodSig D.nd D.naut Sig' := by
  intro k
  have e : (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig' (D.naut.plGw k v))) =
      (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) :=
    funext fun v => (h k v).symm
  have := hg k
  simp only [e] at this ⊢
  exact this

theorem good_labels {Sig : List (Part D.naut.CG)} (hg : goodSig D.nd D.naut Sig) (i : D.nd.Loc) (k : Fin 2)
    (v : D.nd.PlG k) :
    Squarefree (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) ∧
      ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
        ¬ (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).IsRoot
          (u : ZMod (D.host.g k)) := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2⟩ := hg k
  refine ⟨h1.2.1 v, fun u hu hr => ?_⟩
  obtain ⟨ℓ, hℓg, hℓ⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have hℓne : ℓ ≠ D.host.g k := by omega
  have hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈
      Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero (h1.1 v).1)]
    exact hr.map
  rcases hu with rfl | rfl
  · exact h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl
  · exact h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl

end Record

section Series

variable {D : D7}

local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))

theorem eSer_mem (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f) ∈ CZ :=
  atPlace_mem_center D k v _ (D.ntypes.eSer_central k f)

theorem onMt_coe (μ : D.what₂.Tup) (j : ℕ) (c : ↥CZ) :
    D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
  unfold NTypes.onMt
  rw [dif_pos c.2]

theorem series_fix (hSer : GlobalTheory.TypeLeaf.SerLoc D) (i : D.nd.Loc) (σ' : D.ntypes.Par)
    (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hF : F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ')
    (k : Fin 2) (v : D.nd.PlG k) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (D.ntypes.labPar k σ' v))) F = F := by
  classical
  obtain ⟨S, -, hsum⟩ := D.ntypes.eSer_sum k
  have h1 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v 1) F = F := by
    rw [atPlace_one, onMt_one]
    rfl
  rw [← hsum, atPlace_sum, onMt_sum D _ _ S _ (fun f _ => eSer_mem k v f), LinearMap.sum_apply] at h1
  have hz : ∀ f, f ≠ D.ntypes.labPar k σ' v →
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F = 0 := by
    intro f hf
    by_contra hne
    exact hf (hSer i σ' k v f F hF hne)
  by_cases hm : D.ntypes.labPar k σ' v ∈ S
  · rw [Finset.sum_eq_single_of_mem _ hm (fun f _ hf => hz f hf)] at h1
    exact h1
  · rw [Finset.sum_eq_zero (fun f hf => hz f (fun h => hm (h ▸ hf)))] at h1
    rw [← h1, map_zero]

def ef (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]) (kv : Σ k : Fin 2, D.nd.PlG k) : ↥CZ :=
  ⟨Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)), eSer_mem kv.1 kv.2 (s kv)⟩

theorem list_prod_eq (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X])
    (L : List (Σ k : Fin 2, D.nd.PlG k)) (hnd : L.Nodup) (hall : ∀ kv, kv ∈ L) :
    (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod =
      ((∏ kv, ef s kv : ↥CZ) : MonoidAlgebra ℂ (G0g D.nd)) := by
  classical
  have h1 : (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))) =
      (L.map (ef s)).map (Subalgebra.val CZ) := by
    rw [List.map_map]
    rfl
  have h2 : L.toFinset = Finset.univ := Finset.eq_univ_of_forall fun kv => List.mem_toFinset.2 (hall kv)
  rw [h1, ← map_list_prod (Subalgebra.val CZ), ← List.prod_toFinset (ef s) hnd, h2]
  rfl

theorem cen_prod_fix {M : Type} [AddCommGroup M] [Module ℂ M] (cen : ↥CZ →ₐ[ℂ] Module.End ℂ M)
    {ι : Type} (e : ι → ↥CZ) (S : Finset ι) (F : M) (h : ∀ a ∈ S, cen (e a) F = F) :
    cen (∏ a ∈ S, e a) F = F := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, map_one]; rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply,
      ih fun b hb => h b (Finset.mem_insert_of_mem hb), h a (Finset.mem_insert_self a S)]

theorem cen_prod_ne {M : Type} [AddCommGroup M] [Module ℂ M] (cen : ↥CZ →ₐ[ℂ] Module.End ℂ M)
    {ι : Type} [DecidableEq ι] (e : ι → ↥CZ) (S : Finset ι) (F : M) (hne : cen (∏ a ∈ S, e a) F ≠ 0)
    (a : ι) (ha : a ∈ S) : cen (e a) F ≠ 0 := by
  intro h0
  apply hne
  rw [← Finset.prod_erase_mul S e ha, map_mul, Module.End.mul_apply, h0, map_zero]

end Series

section Main

theorem lenUnit_natCast_le {D : D7} (i : D.nd.Loc) (n : ℕ) (hn : n ≠ 0) :
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {(n : D.nd.O i)}) ≤ (padicValNat (D.nd.l i) n : ℚ) := by
  have := D.nd.lPrime i
  have h := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_int (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) (n : ℤ)
    (by exact_mod_cast hn)
  rw [Int.cast_natCast, padicValInt.of_nat] at h
  rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i h]

end Main

theorem main : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → LocalGlobalCompatibilityAlt (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  intro D P hSer hBC hLGC hT0 h5 hEig hCE i k hl π hπ
  classical
  obtain ⟨hπZN, Sig, hSig, hgood⟩ := (D.Zgood_tie i π).1 hπ
  obtain ⟨σ', hσ'⟩ := P.Par_surj i π Sig hSig
  obtain ⟨P0, hP0, hB0⟩ := hSig
  let s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X] := fun kv => D.ntypes.labPar kv.1 σ' kv.2
  obtain ⟨z, L, hLnd, hLall, hz⟩ := hCE i s
  have hz' : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F := by
    intro F
    rw [hz, list_prod_eq s L hLnd hLall]
    rw [show (D.what₂.restRowsFiniteGroupCard : ℂ) • ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) = (((D.what₂.restRowsFiniteGroupCard : ℂ) • ∏ kv, ef s kv :
          ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl,
      onMt_coe, map_smul]
    rfl
  have hfixπ : ∀ PI : D.naut.AV i, D.naut.ptV i PI = some π → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F = F := by
    intro PI hPI F hF
    have hB := bc_all hT0 hLGC h5 hBC hP0 hPI hB0
    have hF' := typeV_le_mtPar hσ' hB hF
    refine cen_prod_fix _ _ _ F fun kv _ => ?_
    rw [← onMt_coe]
    exact series_fix hSer i σ' F hF' kv.1 kv.2
  have hιb : iotaO D.nd D.naut i (D.what₂.restRowsFiniteGroupCard : D.nd.O i) = (D.what₂.restRowsFiniteGroupCard : ℂ) := map_natCast _ _
  have hscal : ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
      (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = (D.what₂.restRowsFiniteGroupCard : D.nd.O i) • u :=
    hEig i z π _ fun PI hPI F hF => by rw [hz', hfixπ PI hPI F hF, hιb]
  let Xs : Set (D.nd.X i) :=
    {x | ∃ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u ≠ 0}
  have hwit : ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
      ∀ kv, D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (ef s kv) F ≠ 0 := by
    rintro x ⟨u, hu, hne⟩
    by_contra hcon
    push Not at hcon
    apply hne
    have h0 := hEig i z x 0 (fun PI hPI F hF => ?_) u hu
    · rw [h0, zero_smul]
    · obtain ⟨kv, hkv⟩ := hcon PI hPI F hF
      rw [hz', map_zero, zero_smul]
      by_contra hc
      have hc' : D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F ≠ 0 := fun h => hc (by rw [h, smul_zero])
      exact cen_prod_ne _ _ _ F hc' kv (Finset.mem_univ kv) hkv
  have hcard : D.what₂.restRowsFiniteGroupCard ≠ 0 := by
    rw [D.nd.restN_card_levelGroup_eq]
    refine Finset.prod_ne_zero_iff.2 fun k' _ => ?_
    have : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
    exact pow_ne_zero _ Nat.card_pos.ne'
  have hb0 : (D.what₂.restRowsFiniteGroupCard : D.nd.O i) ≠ 0 := by
    intro h
    have := congrArg (iotaO D.nd D.naut i) h
    rw [hιb, map_zero] at this
    exact (Nat.cast_ne_zero.2 hcard) this
  have hπX : π ∈ Xs := by
    have hpos : 0 < Module.finrank ℂ ↥(⨆ P ∈ {P | D.naut.ptV i P = some π}, D.naut.typeV i P) := by
      obtain ⟨P2, hP2⟩ := D.naut.pt_surj i π
      refine Nat.pos_of_ne_zero fun h0 => D.naut.typeV_ne i P2 ?_
      have hbot := Submodule.finrank_eq_zero.1 h0
      exact le_bot_iff.1 (hbot ▸ le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) P2 hP2 le_rfl)
    rw [← D.naut.eig_dim i π] at hpos
    have hne : heckeEig (D.nd.T i) (D.nd.act i) π ≠ ⊥ := by
      intro h
      have e : D.nd.mult i π = Module.finrank (FractionRing (D.nd.O i))
          ↥(heckeEig (D.nd.T i) (D.nd.act i) π) := rfl
      rw [e, h, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨u, hu, ?_⟩
    rw [hscal u hu, ← algebraMap_smul (FractionRing (D.nd.O i))]
    refine smul_ne_zero ?_ hu0
    rw [Ne, ← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))]
    exact (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))).ne hb0
  refine ⟨Xs, P.zO i z, (D.what₂.restRowsFiniteGroupCard : D.nd.O i), ⟨hπX, (D.Z_tie i π).2 hπZN, ?_, fun f => P.zO_comm i z f,
    hb0, hscal, fun x hx u hu => ?_, ?_⟩, ?_⟩
  · intro x hx hxZ
    obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
    obtain ⟨Sig1, hS1⟩ := hasParamX_of_Z hT0 h5 hxZ
    obtain ⟨σ1, hσ1⟩ := P.Par_surj i x Sig1 hS1
    obtain ⟨P1, hP1, hB1⟩ := hS1
    have hF1 := typeV_le_mtPar hσ1 (bc_all hT0 hLGC h5 hBC hP1 hPI hB1) hF
    have hlab : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), s kv = D.ntypes.labPar kv.1 σ1 kv.2 := fun kv =>
      hSer i σ1 kv.1 kv.2 (s kv) F hF1
        (by rw [show Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)) = ((ef s kv : ↥(Subalgebra.center ℂ
          (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl, onMt_coe]; exact hne kv)
    have hg1 : goodSig D.nd D.naut Sig1 := goodSig_of_labels (fun k' v => by
      rw [← labPar_eq hσ' k' v, ← labPar_eq hσ1 k' v]; exact hlab ⟨k', v⟩) hgood
    exact (D.Zgood_tie i x).2 ⟨(D.Z_tie i x).1 hxZ, Sig1, ⟨P1, hP1, hB1⟩, hg1⟩
  · by_contra h
    exact hx ⟨u, hu, h⟩
  · rw [← hl]
    exact lenUnit_natCast_le i _ hcard
  · refine ⟨fun v => s ⟨k, v⟩, fun v => ?_, fun x hx => ?_⟩
    · show Squarefree (D.ntypes.labPar k σ' v) ∧ ∀ u : (ZMod (D.host.g k))ˣ,
          u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (D.ntypes.labPar k σ' v).IsRoot (u : ZMod (D.host.g k))
      rw [labPar_eq hσ' k v]
      exact good_labels hgood i k v
    · obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
      refine ⟨PI, hPI, fun v => ?_⟩
      have h1 := hne ⟨k, v⟩
      rw [← onMt_coe] at h1
      change D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s ⟨k, v⟩))) F ≠ 0 at h1
      have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
          Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = s ⟨k, v⟩ then (P.lz k).idem τ else 0) ∈
            Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
        intro τ _
        split_ifs
        · exact atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
        · rw [atPlace_zero]
          exact Subalgebra.zero_mem _
      rw [P.eSer_eq k, atPlace_sum, onMt_sum D _ _ _ _ hc, LinearMap.sum_apply] at h1
      obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      by_cases hlab : (P.lz k).lab τ = s ⟨k, v⟩
      · rw [if_pos hlab] at hτ
        exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
      · exfalso
        apply hτ
        rw [if_neg hlab, atPlace_zero]
        unfold NTypes.onMt
        rw [dif_pos (Subalgebra.zero_mem _)]
        have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
        rw [e0, map_zero]
        rfl

end GlobalTheory.CutAtGood

end
