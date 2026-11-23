import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.Layers
import GroundTheory.GlobalFields.GlobalReciprocity.NormSquare
import GroundTheory.GlobalFields.GlobalReciprocity.LocalSurjective
import GroundTheory.GlobalFields.GlobalReciprocity.DegreeLift
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.PowInvariant

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField GroundTheory.LocalField.Abstract IdeleGroup SemiLocal
open scoped Pointwise GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield _root_.GroundTheory.Global.Cyclotomic ProfiniteInteger

def degreeLevel (m : ℕ+) : Subgroup Gal(ℚ̄/ℚ) :=
  ((AddMonoidHom.toMultiplicative ((proj m : ℤ̂ →+* ZMod m) : ℤ̂ →+ ZMod m)).comp degree).ker

theorem mem_degreeLevel {m : ℕ+} {τ : Gal(ℚ̄/ℚ)} :
    τ ∈ degreeLevel m ↔ proj m (Multiplicative.toAdd (degree τ)) = 0 :=
  Iff.rfl

instance (m : ℕ+) : (degreeLevel m).Normal := MonoidHom.normal_ker _

theorem isOpen_degreeLevel (m : ℕ+) : IsOpen (degreeLevel m : Set Gal(ℚ̄/ℚ)) := by
  have h : (degreeLevel m : Set Gal(ℚ̄/ℚ)) =
      (fun τ ↦ proj m (Multiplicative.toAdd (degree τ))) ⁻¹' {0} := by
    ext τ
    exact mem_degreeLevel
  rw [h]
  exact (isOpen_discrete _).preimage
    ((continuous_proj m).comp (continuous_toAdd.comp continuous_degree))

def layerGroup (L : FiniteSubfield) (m : ℕ+) : OpenSubgroup Gal(ℚ̄/ℚ) :=
  ⟨L.1.fixingSubgroup ⊓ degreeLevel m, L.1.fixingSubgroup_isOpen.inter (isOpen_degreeLevel m)⟩

theorem mem_layerGroup {L : FiniteSubfield} {m : ℕ+} {τ : Gal(ℚ̄/ℚ)} :
    τ ∈ (layerGroup L m : Subgroup Gal(ℚ̄/ℚ)) ↔ τ ∈ L.1.fixingSubgroup ∧ τ ∈ degreeLevel m :=
  Iff.rfl

def layerField (L : FiniteSubfield) (m : ℕ+) : FiniteSubfield :=
  ofOpenSubgroup (layerGroup L m)

theorem fixingSubgroup_layerField (L : FiniteSubfield) (m : ℕ+) :
    (layerField L m).1.fixingSubgroup = layerGroup L m :=
  fixingSubgroup_ofOpenSubgroup _

theorem zpow_conj_mem_layerGroup {K L : FiniteSubfield} (hKL : K ≤ L)
    [hN : (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] (m : ℕ+) {s : Gal(ℚ̄/ℚ)}
    (hs : s ∈ K.1.fixingSubgroup) (k : ℤ) {x : Gal(ℚ̄/ℚ)}
    (hx : x ∈ (layerGroup L m : Subgroup Gal(ℚ̄/ℚ))) :
    s ^ k * x * (s ^ k)⁻¹ ∈ (layerGroup L m : Subgroup Gal(ℚ̄/ℚ)) := by
  refine ⟨?_, (inferInstance : (degreeLevel m).Normal).conj_mem x hx.2 (s ^ k)⟩
  have h1 := hN.conj_mem ⟨x, IntermediateField.fixingSubgroup_le (show K.1 ≤ L.1 from hKL) hx.1⟩
    (Subgroup.mem_subgroupOf.2 hx.1) ⟨s ^ k, zpow_mem hs k⟩
  exact Subgroup.mem_subgroupOf.1 h1

def powerSubgroup (U : Subgroup Gal(ℚ̄/ℚ)) (s : Gal(ℚ̄/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) : Subgroup Gal(ℚ̄/ℚ) := by
  first
  | exact @GroundTheory.Variant₂.N1.mulZPowers U s hU
  | exact GroundTheory.Variant₂.N1.mulZPowers ..
  | (intros; apply GroundTheory.Variant₂.N1.mulZPowers <;> assumption)

theorem le_powerSubgroup (U : Subgroup Gal(ℚ̄/ℚ)) (s : Gal(ℚ̄/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) : U ≤ powerSubgroup U s hU := by
  first
  | exact @GroundTheory.Variant₂.N1.le_powerSubgroup₂ U s hU
  | exact GroundTheory.Variant₂.N1.le_powerSubgroup₂ ..
  | (intros; apply GroundTheory.Variant₂.N1.le_powerSubgroup₂ <;> assumption)

theorem mem_powerSubgroup_self (U : Subgroup Gal(ℚ̄/ℚ)) (s : Gal(ℚ̄/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) : s ∈ powerSubgroup U s hU := by
  first
  | exact @GroundTheory.Variant₂.N1.mem_mulZPowers_self U s hU
  | exact GroundTheory.Variant₂.N1.mem_mulZPowers_self ..
  | (intros; apply GroundTheory.Variant₂.N1.mem_mulZPowers_self <;> assumption)

section Fields

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [hN : (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] (m : ℕ+) (s : Gal(ℚ̄/ℚ))
  (hs : s ∈ K.1.fixingSubgroup)

def powerGroup : OpenSubgroup Gal(ℚ̄/ℚ) :=
  ⟨powerSubgroup (layerGroup L m) s fun k _ hx ↦ zpow_conj_mem_layerGroup hKL.out m hs k hx,
    Subgroup.isOpen_mono (le_powerSubgroup _ _ _) (layerGroup L m).isOpen⟩

def powerField : FiniteSubfield :=
  ofOpenSubgroup (powerGroup K L m s hs)

theorem fixingSubgroup_powerField :
    (powerField K L m s hs).1.fixingSubgroup = powerGroup K L m s hs :=
  fixingSubgroup_ofOpenSubgroup _

theorem ofOpenSubgroup_le {U U' : OpenSubgroup Gal(ℚ̄/ℚ)} (h : U' ≤ U) :
    ofOpenSubgroup U ≤ ofOpenSubgroup U' := fun _ hx ↦
  (IntermediateField.mem_fixedField_iff _ _).2 fun τ hτ ↦
    (IntermediateField.mem_fixedField_iff _ _).1 hx τ (h hτ)

theorem le_ofOpenSubgroup {F : FiniteSubfield} {U : OpenSubgroup Gal(ℚ̄/ℚ)}
    (h : (U : Subgroup Gal(ℚ̄/ℚ)) ≤ F.1.fixingSubgroup) : F ≤ ofOpenSubgroup U := fun x hx ↦
  (IntermediateField.mem_fixedField_iff _ _).2 fun _ hτ ↦
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 (h hτ) x hx

theorem le_layerField : L ≤ layerField L m :=
  le_ofOpenSubgroup fun _ hτ ↦ hτ.1

theorem powerField_le_layerField : powerField K L m s hs ≤ layerField L m :=
  ofOpenSubgroup_le fun x hx ↦ ⟨0, by simpa using hx⟩

theorem le_powerField : K ≤ powerField K L m s hs := by
  refine le_ofOpenSubgroup fun τ ⟨k, u, hu, hτu⟩ ↦ ?_
  have h1 : u ∈ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (show K.1 ≤ L.1 from hKL.out) hu.1
  rw [hτu]
  exact mul_mem (zpow_mem hs k) h1

theorem mem_powerGroup_self : s ∈ (powerGroup K L m s hs : Subgroup Gal(ℚ̄/ℚ)) :=
  ⟨1, 1, one_mem _, by simp⟩

theorem layerField_le_sup_zhatField {g : ℕ}
    (hm : ∀ k : ℤ, proj m ((k : ℤ̂) * Multiplicative.toAdd (degree s)) = 0 → (g : ℤ) ∣ k)
    (hg : ∀ k : ℤ, (g : ℤ) ∣ k → s ^ k ∈ L.1.fixingSubgroup) :
    (layerField L m).1 ≤ (powerField K L m s hs).1 ⊔ zhatField := by
  have hle : (powerField K L m s hs).1.fixingSubgroup ⊓ degree.ker ≤
      (layerField L m).1.fixingSubgroup := by
    rintro τ ⟨hτS, hτ⟩
    rw [SetLike.mem_coe, fixingSubgroup_powerField] at hτS
    obtain ⟨k, hk⟩ : ∃ k : ℤ, s ^ k * τ ∈ (layerGroup L m : Subgroup Gal(ℚ̄/ℚ)) := by
      obtain ⟨k, u, hu, hτu⟩ := hτS
      refine ⟨-k, ?_⟩
      rw [hτu, zpow_neg, inv_mul_cancel_left]
      exact hu
    rw [fixingSubgroup_layerField]
    have hd : degree (s ^ k * τ) = degree s ^ k := by
      rw [map_mul, MonoidHom.mem_ker.1 hτ, mul_one, map_zpow]
    have hk0 : proj m ((k : ℤ̂) * Multiplicative.toAdd (degree s)) = 0 := by
      have := mem_degreeLevel.1 hk.2
      rwa [hd, toAdd_zpow, zsmul_eq_mul] at this
    have hsk : s ^ k ∈ (layerGroup L m : Subgroup Gal(ℚ̄/ℚ)) := by
      refine ⟨hg k (hm k hk0), mem_degreeLevel.2 ?_⟩
      rwa [map_zpow, toAdd_zpow, zsmul_eq_mul]
    have := mul_mem (inv_mem hsk) hk
    rwa [inv_mul_cancel_left] at this
  rw [← fixingSubgroup_zhatField, ← IntermediateField.fixingSubgroup_sup] at hle
  rw [← InfiniteGalois.fixedField_fixingSubgroup ((powerField K L m s hs).1 ⊔ zhatField)]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff]
  intro τ hτ
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle hτ) x hx

end Fields

theorem restrictNormal_restrictScalars_restrictHom {F E F' E' : FiniteSubfield} [Fact (F ≤ E)]
    [Fact (F' ≤ E')] [hFF' : Fact (F ≤ F')] [Fact (E ≤ E')] [Fact (F ≤ E')]
    [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]
    [(E'.1.fixingSubgroup.subgroupOf F'.1.fixingSubgroup).Normal] (g : F'.1.fixingSubgroup) :
    ((restrictHom (E := E') g).restrictScalars F.1).restrictNormal E.1 =
      restrictHom (E := E) (⟨g, IntermediateField.fixingSubgroup_le
        (show F.1 ≤ F'.1 from hFF'.out) g.2⟩ : F.1.fixingSubgroup) := by
  refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
  exact congrArg (fun z : E'.1 ↦ (z : ℚ̄))
    (AlgEquiv.restrictNormal_commutes ((restrictHom (E := E') g).restrictScalars F.1) E.1 x)

section Main

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [hN : (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]
  [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem exists_abstractSymbol_eq_localSymbol (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] (hP : P ≠ ⊥)
    (s : Gal(ℚ̄/ℚ)) (hsK : s ∈ K.1.fixingSubgroup) (hsP : s ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P)
    (hh : ∀ q : Nat.Primes, toPadicInt q (Multiplicative.toAdd (degree s)) ≠ 0) :
    ∃ y : ((FiniteSubfield.placeBelow P hP K).adicCompletion K.1)ˣ,
      abstractSymbol K L (IdeleClassGroup.mk K.1 (finiteEmbedding _ y)) =
        Abelianization.of (restrictHom (E := L) (⟨s, hsK⟩ : K.1.fixingSubgroup)) ∧
      localSymbol L.1 _ y = restrictHom (E := L) (⟨s, hsK⟩ : K.1.fixingSubgroup) := by

  set g := Nat.card (L.1 ≃ₐ[K.1] L.1) with hgdef
  have hg0 : 0 < g := Nat.card_pos
  obtain ⟨m, hm⟩ := exists_pnat_forall_dvd _ hh hg0
  have hgs : ∀ k : ℤ, (g : ℤ) ∣ k → s ^ k ∈ L.1.fixingSubgroup := by
    rintro k ⟨j, rfl⟩
    have h1 : restrictHom (E := L) ((⟨s, hsK⟩ : K.1.fixingSubgroup) ^ ((g : ℤ) * j)) = 1 := by
      rw [map_zpow, zpow_mul, zpow_natCast, hgdef, pow_card_eq_one', one_zpow]
    rw [← MonoidHom.mem_ker, ker_restrictHom, Subgroup.mem_subgroupOf] at h1
    simpa using h1

  set M := layerField L m with hMdef
  set S := powerField K L m s hsK with hSdef
  have : Fact (L ≤ M) := ⟨le_layerField L m⟩
  have : Fact (S ≤ M) := ⟨powerField_le_layerField K L m s hsK⟩
  have hKS : Fact (K ≤ S) := ⟨le_powerField K L m s hsK⟩
  have : Fact (K ≤ M) := ⟨hKL.out.trans (le_layerField L m)⟩
  have hMsup : M.1 ≤ S.1 ⊔ zhatField := layerField_le_sup_zhatField K L m s hsK hm hgs
  have : (M.1.fixingSubgroup.subgroupOf S.1.fixingSubgroup).Normal :=
    normal_of_le_sup_zhatField S M (Fact.out) hMsup
  have : IsMulCommutative (M.1 ≃ₐ[S.1] M.1) := isMulCommutative_of_le_sup_zhatField S M hMsup
  have hsS : s ∈ S.1.fixingSubgroup := by
    rw [hSdef, fixingSubgroup_powerField]
    exact mem_powerGroup_self K L m s hsK

  have hsbar : restrictHom (E := M) (⟨s, hsS⟩ : S.1.fixingSubgroup) ∈
      MulAction.stabilizer (M.1 ≃ₐ[S.1] M.1) (FiniteSubfield.placeBelow P hP M).asIdeal :=
    restrictHom_mem_stabilizer hP _ hsP
  let wM : PlacesOver M.1 (FiniteSubfield.placeBelow P hP S) :=
    ⟨FiniteSubfield.placeBelow P hP M, inferInstance⟩
  obtain ⟨y, hy⟩ := exists_localSymbol_eq (FiniteSubfield.placeBelow P hP S) wM hsbar

  have ha : abstractSymbol S M
      (IdeleClassGroup.mk S.1 (finiteEmbedding (FiniteSubfield.placeBelow P hP S) y)) =
        Abelianization.of (restrictHom (E := M) (⟨s, hsS⟩ : S.1.fixingSubgroup)) := by
    rw [abstractSymbol_mk_of_le_sup_zhatField S M hMsup, ideleSymbol_finiteEmbedding, hy]

  have hb := abstractSymbol_ideleClassNorm (K := K) (L := L) (K' := S) (L' := M) hKS.out
    (le_layerField L m) _ _ ha

  have hc := mk_finiteEmbedding_normUnits (K := K.1) (L := S.1) (FiniteSubfield.placeBelow P hP K)
    ⟨FiniteSubfield.placeBelow P hP S, inferInstance⟩ y

  have hd := restrictNormal_localSymbol_norm (K := K.1) (K' := S.1) (L := L.1) (L' := M.1)
    (FiniteSubfield.placeBelow P hP K) (FiniteSubfield.placeBelow P hP S) y
  rw [hy, restrictNormal_restrictScalars_restrictHom] at hd
  refine ⟨_, ?_, hd.symm⟩
  rw [hc]
  exact hb

theorem abstractSymbol_mk_finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1))
    (x : (v.adicCompletion K.1)ˣ) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 (finiteEmbedding v x)) =
      Abelianization.of (localSymbol L.1 v x) := by
  obtain ⟨P, hPp, hP, rfl⟩ := exists_placeBelow_eq K v
  set σ := localSymbol L.1 (FiniteSubfield.placeBelow P hP K) x with hσdef

  let wL : PlacesOver L.1 (FiniteSubfield.placeBelow P hP K) :=
    ⟨FiniteSubfield.placeBelow P hP L, inferInstance⟩
  have hσw : σ ∈ MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (FiniteSubfield.placeBelow P hP L).asIdeal :=
    localSymbol_mem_stabilizer L.1 _ wL x

  obtain ⟨τ, hτ⟩ := restrictHom_surjective (F := K) (E := L) σ
  obtain ⟨σ₀, hσ₀P, hσ₀⟩ := exists_mem_stabilizer_restrictHom_eq hP τ (by rw [hτ]; exact hσw)
  obtain ⟨p, hp, hpP⟩ := exists_liesOver_prime P hP
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, hhP, hhL, hh⟩ := exists_mem_stabilizer_toPadicInt_ne_zero P p L (σ₀ : Gal(ℚ̄/ℚ))
  have hhK : h ∈ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (show K.1 ≤ L.1 from hKL.out) hhL
  have hsK : (σ₀ : Gal(ℚ̄/ℚ)) * h ∈ K.1.fixingSubgroup := mul_mem σ₀.2 hhK
  have hsσ : restrictHom (E := L) (⟨(σ₀ : Gal(ℚ̄/ℚ)) * h, hsK⟩ : K.1.fixingSubgroup) = σ := by
    have h1 : restrictHom (E := L) (⟨h, hhK⟩ : K.1.fixingSubgroup) = 1 := by
      rw [← MonoidHom.mem_ker, ker_restrictHom]
      exact Subgroup.mem_subgroupOf.2 hhL
    rw [show (⟨(σ₀ : Gal(ℚ̄/ℚ)) * h, hsK⟩ : K.1.fixingSubgroup) = σ₀ * ⟨h, hhK⟩ from rfl, map_mul,
      h1, mul_one, hσ₀, hτ]
  obtain ⟨y, hy1, hy2⟩ := exists_abstractSymbol_eq_localSymbol K L P hP _ hsK (mul_mem hσ₀P hhP) hh
  rw [hsσ] at hy1 hy2

  have he : x * y⁻¹ ∈ (localSymbol L.1 (FiniteSubfield.placeBelow P hP K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy2, hσdef, mul_inv_cancel]
  rw [ker_localSymbol L.1 _ wL] at he
  obtain ⟨z, hz⟩ := he
  have hx : x = y * LocalField.normUnits ((FiniteSubfield.placeBelow P hP K).adicCompletion K.1)
      (wL.1.adicCompletion L.1) z := by
    rw [hz, mul_left_comm, mul_inv_cancel, mul_one]
  have h2 : abstractSymbol K L (IdeleClassGroup.mk K.1 (finiteEmbedding
      (FiniteSubfield.placeBelow P hP K) (LocalField.normUnits
        ((FiniteSubfield.placeBelow P hP K).adicCompletion K.1) (wL.1.adicCompletion L.1) z))) = 1 := by
    rw [mk_finiteEmbedding_normUnits (K := K.1) (L := L.1) (FiniteSubfield.placeBelow P hP K) wL z]
    exact abstractSymbol_ideleClassNorm_eq_one K L _
  rw [hx, map_mul, map_mul, map_mul, hy1, h2, mul_one]

theorem abstractSymbol_comp_finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) :
    ((abstractSymbol K L).comp (IdeleClassGroup.mk K.1)).comp (finiteEmbedding v) =
      Abelianization.of.comp (localSymbol L.1 v) :=
  MonoidHom.ext fun x ↦ abstractSymbol_mk_finiteEmbedding K L v x

end Main

end IdeleClassLimit

end

end GroundTheory.Global
