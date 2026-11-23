import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InertLocalIndices
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeRowsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

theorem repr_map {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis A b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem coord_eq_zero {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (h : Algebra.TensorProduct.map φ (AlgHom.id F E) z = 0) (i : ι) :
    φ ((Algebra.TensorProduct.basis A b).repr z i) = 0 := by
  rw [← repr_map, h, map_zero, Finsupp.zero_apply]

theorem coord_eq_zero₂ {F E A B C ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [CommRing C] [Algebra F A]
    [Algebra F B] [Algebra F C] (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (ψ : B →ₐ[F] C) (z : A ⊗[F] E)
    (h : Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = 0) (i : ι) :
    ψ (φ ((Algebra.TensorProduct.basis A b).repr z i)) = 0 := by
  rw [← repr_map, coord_eq_zero b ψ _ h]

theorem mul_eq_of_coord {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    (b : Module.Basis ι F E) (ε : A) (z : A ⊗[F] E)
    (h : ∀ i, ε * (Algebra.TensorProduct.basis A b).repr z i = (Algebra.TensorProduct.basis A b).repr z i) :
    algebraMap A (A ⊗[F] E) ε * z = z := by
  rw [← Algebra.smul_def]
  refine (Algebra.TensorProduct.basis A b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h]

theorem pair_mul_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (a1 : evalV F v α = 1)
    (a : AF F) (e0 : fstA F a = 0) (e1 : ∀ v', v' ≠ v → evalV F v' (sndA F a) = 0) : pairA F 0 α * a = a := by
  refine Prod.ext ((zero_mul (fstA F a)).trans e0.symm) (FiniteAdeleRing.ext _ fun w => ?_)
  change evalV F w (α * sndA F a) = evalV F w (sndA F a)
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    rw [a1, one_mul]
  · rw [e1 w hw, mul_zero]

theorem map_eq_one_iff {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) {n : ℕ} (m : Matrix (Fin n) (Fin n) R) :
    m.map π = 1 ↔ ∀ i j, π ((m - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isDC_image {H G : Type} [Group H] [Group G] [DecidableEq G] (φ : H →* G) (N : Subgroup H) {J L : Subgroup G}
    (hs : GlobalTheory.HkB.LocSplit J L) (K : Set H) (hi : ∀ g ∈ N, φ g = 1 → g = 1) (hKN : ∀ k ∈ K, k ∈ N) (h1 : (1 : H) ∈ K)
    (hKJ : ∀ k ∈ K, φ k ∈ J) (hJK : ∀ y ∈ J, y ∈ L → ∃ k ∈ K, φ k = y) {g : H} (hg : φ g ∈ L) {R : Finset H}
    (hL : ∀ γ ∈ R, φ γ ∈ L) (hR1 : ∀ γ ∈ R, γ ∈ N ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂)
    (hR2 : ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    Bridge.IsDC J (φ g) (R.image φ) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR1 γ hγ
    exact ⟨⟨φ k₁, hKJ _ h₁⟩, ⟨φ k₂, hKJ _ h₂⟩, by simp only [map_mul]⟩
  · rintro _ ⟨k₁, k₂, rfl⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, haL, e₁, c₁⟩ := hs k₁ k₁.2
    obtain ⟨κ, hκ, rfl⟩ := hJK a₁ ha₁ haL
    obtain ⟨γ, ⟨hγ, hγK⟩, -⟩ := hR2 (κ * g) ⟨κ, hκ, 1, h1, (mul_one _).symm⟩
    have hmem : (φ γ)⁻¹ * (k₁ * φ g * k₂) ∈ J := by
      have : (φ γ)⁻¹ * ((k₁ : G) * φ g * k₂) = φ (γ⁻¹ * (κ * g)) * (b₁ * k₂) := by
        rw [e₁, mul_assoc (φ κ) b₁, (c₁ _ hg).eq]
        simp only [map_mul, map_inv, mul_assoc]
      rw [this]
      exact J.mul_mem (hKJ _ hγK) (J.mul_mem hb₁ k₂.2)
    refine ⟨φ γ, ⟨Finset.mem_image_of_mem _ hγ, hmem⟩, ?_⟩
    rintro a' ⟨ha', hmem'⟩
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 ha'
    have h2 : (φ γ)⁻¹ * φ γ' ∈ J := by
      have : (φ γ)⁻¹ * φ γ' = ((φ γ)⁻¹ * ((k₁ : G) * φ g * k₂)) * ((φ γ')⁻¹ * (k₁ * φ g * k₂))⁻¹ := by group
      rw [this]
      exact J.mul_mem hmem (J.inv_mem hmem')
    obtain ⟨κ', hκ', e'⟩ := hJK _ h2 (L.mul_mem (L.inv_mem (hL γ hγ)) (hL γ' hγ'))
    have h3 : κ'⁻¹ * (γ⁻¹ * γ') = 1 :=
      hi _ (N.mul_mem (N.inv_mem (hKN _ hκ')) (N.mul_mem (N.inv_mem (hR1 γ hγ).1) (hR1 γ' hγ').1))
        (by rw [map_mul, map_inv, e', map_mul, map_inv, inv_mul_cancel])
    have h4 : γ⁻¹ * γ' ∈ K := inv_mul_eq_one.1 h3 ▸ hκ'
    rw [(hR2 γ' (hR1 γ' hγ').2).unique ⟨hγ', by rw [inv_mul_cancel]; exact h1⟩ ⟨hγ, h4⟩]

theorem mem_iff_range {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) {x : X} : x ∈ V ↔ x ∈ LinearMap.range M.e := by
  rw [h.2.1]

theorem exists_op {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : HMod (G → W))
    (hM : Function.Injective M.e) (B : Finset G) (h : ∀ f, Bridge.dcOp B (M.e f) ∈ LinearMap.range M.e) :
    ∃ U : Module.End ℂ M.H, ∀ f, M.e (U f) = Bridge.dcOp B (M.e f) := by
  choose u hu using h
  refine ⟨⟨⟨u, fun f g => hM ?_⟩, fun c f => hM ?_⟩, hu⟩
  · rw [map_add, hu, hu, hu, map_add]
    funext x
    simp [Bridge.dcOp, Finset.sum_add_distrib]
  · rw [RingHom.id_apply, map_smul, hu, hu, map_smul]
    funext x
    simp [Bridge.dcOp, Finset.smul_sum]

end Generic

variable {D : D7}

section Inert

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {P : Pl D.host.E}

theorem under_eq (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) : P.under (𝓞 D.host.F) = v :=
  HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 (le_of_eq h))).symm

theorem inertOver_iff : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P ↔ IndefiniteRowSideFullHecke.HeckeIntertwinersInert.IsInertPl P ∧ IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF P = v := by
  constructor
  · intro h
    obtain rfl := under_eq h
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact h

theorem eq_of_under (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v) : Q = P := by
  refine (GlobalTheory.IdemSupport.eq_of_le ?_).symm
  rw [← (h : _ = P.asIdeal), Ideal.map_le_iff_le_comap, ← hQ]
  exact le_rfl

theorem star_eq_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x

theorem offG_of_inert (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun k hk => by
    have h1 := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
    have h2 : GlobalTheory.IdemSupport.cP P = P := eq_of_under h ((GlobalTheory.IdemSupport.under_cP P).trans (under_eq h))
    obtain ⟨x, hx, hy⟩ := h1
    rw [← h2] at hx
    exact hy _ ((GlobalTheory.IdemSupport.cO_coe x).trans (star_eq_conj (x : D.host.E))) ((GlobalTheory.IdemSupport.mem_cP P x).1 hx)
  intro hg
  rw [Nat.cast_mul] at hg
  exact (P.isPrime.mem_or_mem hg).elim (key 0) (key 1)

theorem exists_unif (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) : ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E,
    (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  by_contra hn
  have h1 : P.asIdeal ≤ P.asIdeal ^ 2 := by
    conv_lhs => rw [← (h : _ = P.asIdeal)]
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    by_contra h2
    exact hn ⟨x, algebraMap _ _ x, rfl, (h : _ = P.asIdeal) ▸ Ideal.mem_map_of_mem _ hx, h2⟩
  have h2 := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
  rw [pow_one] at h2
  exact h2.not_ge h1

theorem isPrimeIdem_of_inert (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    IsPrimeIdem P (algebraMap _ (Formalism.L2.Theta.AE D) ε) (algebraMap _ _ ε) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.IdemSupport.place_comp hΦ hε
  exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, (GlobalTheory.IdemSupport.tie_iff hΦ (GlobalTheory.IdemSupport.place_idem hΦ hε) h0 P).2
    ⟨h0, h1 P (under_eq h), fun Q hQ => h2 Q fun e => hQ (eq_of_under h e)⟩⟩

end Inert

section Local

variable (V : HSp D)

theorem locAt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) :
    IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := Iff.rfl

def cmp (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

def locGrp (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Bridge.Gf V) :=
  ⨅ (v') (_ : v' ≠ v), ((Formalism.UG.bc (cmp D v')).comp (finHom V).range.subtype).ker

theorem mem_locGrp {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Bridge.Gf V} : x ∈ locGrp V v ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := by
  simp only [locGrp, Subgroup.mem_iInf]
  exact forall₂_congr fun v' _ => ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

abbrev fin : GA D V →* Bridge.Gf V := (finHom V).rangeRestrict

theorem idem_mul_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (z : Formalism.L2.Theta.AE D)
    (h0 : infPart D z = 0) (h1 : ∀ v', v' ≠ v → cmp D v' (finPart D z) = 0) : algebraMap _ (Formalism.L2.Theta.AE D) ε * z = z := by
  obtain ⟨α, rfl, a1, -⟩ := hε
  exact mul_eq_of_coord (Module.finBasis D.host.F D.host.E) _ z fun i => pair_mul_eq a1 _
    (coord_eq_zero _ (fstA D.host.F) z h0 i) fun v' hv => coord_eq_zero₂ _ (sndA D.host.F) (evalV D.host.F v') z (h1 v' hv) i

theorem suppF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {g : GA D V}
    (hg : g ∈ GfC V) : SuppF V (algebraMap _ _ ε) g ↔ fin V g ∈ locGrp V v := by
  have key : ∀ v', (Units.val (finHom V g)).map (cmp D v') = (Formalism.L2.Theta.mt V g).map ((cmp D v').comp (finPart D)) :=
    fun _ => rfl
  rw [mem_locGrp]
  constructor
  · intro h v' hv
    refine (key v').trans ((map_eq_one_iff _ _).2 fun i j => ?_)
    obtain ⟨α, rfl, -, a0⟩ := hε
    have h2 : (cmp D v').comp (finPart D) (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) = 0 := by
      change evalV D.host.F v' α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [a0 v' hv, TensorProduct.zero_tmul]
    rw [← h i j, RingHom.map_mul, h2, zero_mul]
  · intro h i j
    have h0 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    exact idem_mul_eq hε _ ((map_eq_one_iff _ _).1 h0 i j)
      fun v' hv => (map_eq_one_iff _ _).1 ((key v').symm.trans (h v' hv)) i j

theorem fin_inj (g : GA D V) (hg : g ∈ GfC V) (h : fin V g = 1) : g = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h0 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h1 : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val (congrArg Subtype.val h)
  refine GlobalTheory.IdemSupport.mt_inj V ((GlobalTheory.IdemSupport.mt_one V).symm ▸ sub_eq_zero.1 (Matrix.ext fun i j => e.injective ?_))
  rw [Matrix.zero_apply, map_zero]
  exact Prod.ext ((he _).1.trans ((map_eq_one_iff _ _).1 h0 i j)) ((he _).2.trans ((map_eq_one_iff _ _).1 h1 i j))

theorem fin_lift (x : Bridge.Gf V) : ∃ g ∈ GfC V, fin V g = x := by
  obtain ⟨x, g, rfl⟩ := x
  let f : Formalism.L2.Theta.AE D := algebraMap _ _ (pairA D.host.F 0 1)
  have hp : pairA D.host.F 0 1 * pairA D.host.F 0 1 = pairA D.host.F 0 1 :=
    Prod.ext (mul_zero (0 : Ainf D.host.F)) (mul_one (1 : Af D.host.F))
  have hff : f * f = f := by rw [← RingHom.map_mul, hp]
  obtain ⟨g₁, g₂, h₁, h₂, rfl⟩ := GlobalTheory.IdemSupport.exists_split V hff (GlobalTheory.IdemSupport.cA_algebraMap _) g
  have b : finHom V g₂ = 1 := by
    refine Units.ext ((map_eq_one_iff (finPart D) _).2 fun i j => ?_)
    have h3 : finPart D (1 - f) = 0 := by
      rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero]
      rfl
    refine (congrArg (finPart D) (h₂ i j)).symm.trans ?_
    rw [RingHom.map_mul, h3, zero_mul]
  refine ⟨g₁, GlobalTheory.IdemSupport.mem_GfC_of_suppF V (TensorProduct.zero_tmul _ _) h₁, Subtype.ext ?_⟩
  show finHom V g₁ = finHom V (g₁ * g₂)
  rw [map_mul, b, mul_one]

set_option maxHeartbeats 1000000 in

theorem local_data (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1) {v : HeightOneSpectrum (𝓞 D.host.F)} {P : Pl D.host.E}
    (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) (hg : P ∉ L.Pg) (hq : P ∉ L.Q) :
    GlobalTheory.HkB.LocSplit (levEnv V β L).J (locGrp V v) ∧
      (∀ k : (levEnv V β L).J, (k : Bridge.Gf V) ∈ locGrp V v → (levEnv V β L).χ k = 1) ∧
      ∀ x ∈ locGrp V v, ∃ B : Finset (Bridge.Gf V), Bridge.IsDC (levEnv V β L).J x B ∧ ∀ b ∈ B, b ∈ locGrp V v := by
  classical
  refine (GlobalTheory.IdemSupport.exists_placeIdem (D := D) v).elim fun ε hε => ?_
  have hP := isPrimeIdem_of_inert h hε
  have h01 := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P _ _ hP
  have hoff : ∀ PP, PP ∈ (flag1L L).Pg ∨ PP ∈ (flag1L L).Q → PP ≠ P ∧ ¬ IsConjPl PP P := fun PP hPP => by
    have h1 : PP ≠ P := fun e => by
      subst e
      exact hPP.elim hg hq
    refine ⟨h1, fun hc => h1 (eq_of_under h ?_)⟩
    rw [← GlobalTheory.IdemSupport.under_cP, ← (GlobalTheory.IdemSupport.isConjPl_iff PP P).1 hc]
    exact under_eq h
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L) hβ).2 P _ _ hP h1 hoff
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  have hJ : ∀ g ∈ GfC V, fin V g ∈ (levEnv V β L).J ↔ g ∈ levG V β (flag1L L) := fun g hg => ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩
  have hlift : ∀ x ∈ locGrp V v, ∃ g, SuppF V (algebraMap _ _ ε) g ∧ fin V g = x := fun x hx => by
    obtain ⟨g, hg, rfl⟩ := fin_lift V x
    exact ⟨g, (suppF_iff V hε hg).2 hx, rfl⟩
  have hloc : ∀ g, SuppF V (algebraMap _ _ ε) g → fin V g ∈ locGrp V v := fun g hg => (suppF_iff V hε (h01.2.2.1 g hg)).1 hg
  have hs : GlobalTheory.HkB.LocSplit (levEnv V β L).J (locGrp V v) := by
    intro k hk
    obtain ⟨g, hg, rfl⟩ := fin_lift V k
    obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp g ((hJ g hg).1 hk)
    refine ⟨fin V k₁, (hJ _ h₁.1).2 h₁, fin V k₂, (hJ _ h₂.1).2 h₂, hloc _ s₁, map_mul _ _ _, fun l hl => ?_⟩
    obtain ⟨l', hl', rfl⟩ := hlift l hl
    exact (GlobalTheory.IdemSupport.commute_of_suppF V (by rw [mul_sub, mul_one, h01.1, sub_self]) hl' s₂).symm.map (fin V)
  refine ⟨hs, ?_, fun x hx => ?_⟩
  · rintro ⟨k, hk⟩ hl
    obtain ⟨g, hg, rfl⟩ := hlift k hl
    exact Units.ext (hχ g ((hJ g (h01.2.2.1 g hg)).1 hk) hg)
  · obtain ⟨g, hg, rfl⟩ := hlift x hx
    obtain ⟨R, hR, hc⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ hP (exists_unif h) g hg).2.1
    refine ⟨R.image (fin V), isDC_image (fin V) (GfC V) hs {k | k ∈ KsphC V ∅ ∧ SuppF V (algebraMap _ _ ε) k} (fin_inj V) (fun k hk => h01.2.2.1 k hk.2)
      ⟨GlobalTheory.InertDoubleCoset.one_mem_KsphC V, (GlobalTheory.IdemSupport.suppGroup V _).one_mem⟩
      (fun k hk => (hJ k (h01.2.2.1 k hk.2)).2 ((hK k hk.2).2 hk.1)) (fun y hy hl => ?_) hx
      (fun γ hγ => hloc γ (hR γ hγ)) hc.1 hc.2, fun b hb => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hlift y hl
      exact ⟨k, ⟨(hK k hk).1 ((hJ k (h01.2.2.1 k hk)).1 hy), hk⟩, rfl⟩
    · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hb
      exact hloc γ (hR γ hγ)

end Local

section Compare

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

def forget {t : T} (i : IndefiniteRowSideFullHecke.HeckeIntertwinersInert.InertIx R t) : IndefiniteRowSideFullHecke.InertLocalIndices.InertIx R t :=
  ⟨IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF i.1.1, i.1.1, i.2.1, offG_of_inert i.2.1, i.2.2.1, i.2.2.2.1, i.1.2.1, i.2.2.2.2.1⟩

def withReps {t : T} (i : IndefiniteRowSideFullHecke.InertLocalIndices.InertIx R t) (B : Finset (Bridge.Gf D.sp.X'))
    (h1 : Bridge.IsDC (IndefiniteRowSideFullHecke.InertLocalIndices.levX R t) i.x B) (h2 : ∀ a ∈ B, IndefiniteRowSideFullHecke.InertLocalIndices.LocAt D.sp.X' i.v a) :
    IndefiniteRowSideFullHecke.HeckeIntertwinersInert.InertIx R t :=
  ⟨(i.P, i.x, B), (inertOver_iff.1 i.inert).1, i.offS, i.offQ, (inertOver_iff.1 i.inert).2.symm ▸ i.loc,
    (inertOver_iff.1 i.inert).2.symm ▸ h2, h1⟩

theorem forget_withReps {t : T} (i : IndefiniteRowSideFullHecke.InertLocalIndices.InertIx R t) (B : Finset (Bridge.Gf D.sp.X'))
    (h1 : Bridge.IsDC (IndefiniteRowSideFullHecke.InertLocalIndices.levX R t) i.x B) (h2 : ∀ a ∈ B, IndefiniteRowSideFullHecke.InertLocalIndices.LocAt D.sp.X' i.v a) :
    forget (withReps i B h1 h2) = i := by
  obtain ⟨v, P, h, _, _, _, x, _⟩ := i
  obtain rfl := under_eq h
  rfl

theorem local_at (hC : R.Char F) {t : T} (i : IndefiniteRowSideFullHecke.InertLocalIndices.InertIx R t) :
    GlobalTheory.HkB.LocSplit (IndefiniteRowSideFullHecke.InertLocalIndices.levX R t) (locGrp D.sp.X' i.v) ∧
      (∀ k : IndefiniteRowSideFullHecke.InertLocalIndices.levX R t, (k : Bridge.Gf D.sp.X') ∈ locGrp D.sp.X' i.v →
        (levEnv D.sp.X' R.βX (R.datXt t)).χ k = 1) ∧
      ∀ x ∈ locGrp D.sp.X' i.v, ∃ B : Finset (Bridge.Gf D.sp.X'),
        Bridge.IsDC (IndefiniteRowSideFullHecke.InertLocalIndices.levX R t) x B ∧ ∀ b ∈ B, b ∈ locGrp D.sp.X' i.v :=
  hC.lev.βX.elim fun _ hc =>
    local_data D.sp.X' R.βX R.ΛX (R.datXt t) (by rwa [one_pow] at hc) i.inert (fun h => i.offS (hC.fam.Sb h)) i.offQ

theorem e_mem (hC : R.Char F) (t : T) (f : (R.HX t).H) :
    (R.HX t).e f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ :=
  (mem_iff_range (hC.models.HX t)).2 (LinearMap.mem_range_self _ f)

theorem forget_surjective (hC : R.Char F) (t : T) : Function.Surjective (forget (R := R) (t := t)) := fun i =>
  ((local_at hC i).2.2 i.x ((mem_locGrp _).2 i.loc)).elim fun B h =>
    ⟨_, forget_withReps i B h.1 fun a ha => (mem_locGrp _).1 (h.2 a ha)⟩

theorem exists_isInertOp (hC : R.Char F) {t : T} (i : IndefiniteRowSideFullHecke.HeckeIntertwinersInert.InertIx R t) : ∃ U, IndefiniteRowSideFullHecke.HeckeIntertwinersInert.IsInertOp R t i U :=
  exists_op (R.HX t) (hC.models.HX t).1 i.1.2.2 fun f => by
    have h := local_at hC (forget i)
    exact (mem_iff_range (hC.models.HX t)).1 (GlobalTheory.HkB.LocSplit.dcOp_mem _ _ h.1 h.2.1 i.2.2.2.2.2.2
      (fun a ha => (mem_locGrp _).2 (i.2.2.2.2.2.1 a ha)) (e_mem hC t f))

theorem exists_inertTie (hC : R.Char F) : ∃ TI, IndefiniteRowSideFullHecke.InertLocalIndices.InertTie R TI := by
  choose s hs using forget_surjective hC
  choose U hU using fun t i => exists_isInertOp hC (s t i)
  refine ⟨U, fun t i => ⟨(s t i).1.2.2, ?_, ?_, hU t i⟩⟩
  · have := (s t i).2.2.2.2.2.2
    rwa [show (s t i).1.2.1 = i.x from congrArg IndefiniteRowSideFullHecke.InertLocalIndices.InertIx.x (hs t i)] at this
  · have := (s t i).2.2.2.2.2.1
    rwa [show IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF (s t i).1.1 = i.v from congrArg IndefiniteRowSideFullHecke.InertLocalIndices.InertIx.v (hs t i)] at this

end Compare

end GlobalTheory.HeckeRowsCompare

end
