import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn princAt resS intGL frGL)

section RedA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev iA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    E →+* E ⊗[F] Formalism.L2.Herm.Af F :=
  Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)

def IntAtA (P : Pl E) (a : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E

def redA (P : Pl E) (a : E ⊗[F] Formalism.L2.Herm.Af F) : kP P :=
  open Classical in
  if h : ∃ c : kP P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E,
      Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩
  then h.choose else 0

def pullV {n : ℕ} (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : Fin n → E) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F :=
  ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ fun i => iA F E (v i)

end RedA

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def mirab (κ : Type) [CommRing κ] (n : ℕ) [NeZero n] : Subgroup (GL (Fin n) κ) where
  carrier := {g | ∀ j, (g : Matrix (Fin n) (Fin n) κ) (lastIdx n) j = if j = lastIdx n then 1 else 0}
  one_mem' := by
    intro j
    show (1 : Matrix (Fin n) (Fin n) κ) (lastIdx n) j = _
    rw [Matrix.one_apply]
    by_cases h : j = lastIdx n
    · simp [h]
    · simp [h, Ne.symm h]
  mul_mem' := by
    intro x y hx hy j
    show ((x : Matrix (Fin n) (Fin n) κ) * (y : Matrix (Fin n) (Fin n) κ)) (lastIdx n) j = _
    rw [Matrix.mul_apply, Finset.sum_eq_single (lastIdx n)]
    · rw [hx (lastIdx n), if_pos rfl, one_mul, hy j]
    · intro l _ hl
      rw [hx l, if_neg hl, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  inv_mem' := by
    intro x hx j
    have h1 : ((x * x⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) (lastIdx n) j =
        (1 : Matrix (Fin n) (Fin n) κ) (lastIdx n) j := by rw [mul_inv_cancel]; rfl
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (lastIdx n)] at h1
    · rw [hx (lastIdx n), if_pos rfl, one_mul] at h1
      rw [h1, Matrix.one_apply]
      by_cases h : j = lastIdx n
      · simp [h]
      · simp [h, Ne.symm h]
    · intro l _ hl
      rw [hx l, if_neg hl, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ)

abbrev URat : Subgroup (GL (Fin n) E) := Formalism.L2.DIV.UR hc (1 : Matrix (Fin n) (Fin n) E)

abbrev UAd : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := Formalism.L2.DIV.UA hc (1 : Matrix (Fin n) (Fin n) E)

theorem ad_gram_hStd : Formalism.UG.gram (hStd E n) = 1 := by
  ext i j
  show (∑ k, star (Pi.single i (1 : E) k) * Pi.single j (1 : E) k) = (1 : Matrix (Fin n) (Fin n) E) i j
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, star_one, one_mul, Pi.single_apply, Matrix.one_apply]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

def ratHom : URat hc n →* UF E n where
  toFun γ := ⟨Formalism.UG.glEquiv (γ : GL (Fin n) E), by
    have h := (Formalism.UG.Final.HermBridge E (Fin n) (hStd E n) (γ : GL (Fin n) E)).1
    rw [ad_gram_hStd] at h
    exact h γ.2⟩
  map_one' := by
    apply Subtype.ext
    show Formalism.UG.glEquiv (1 : GL (Fin n) E) = 1
    ext x i
    simp [Formalism.UG.glEquiv]
  map_mul' := by
    intro a b
    apply Subtype.ext
    show Formalism.UG.glEquiv ((a : GL (Fin n) E) * (b : GL (Fin n) E)) = Formalism.UG.glEquiv (a : GL (Fin n) E) * Formalism.UG.glEquiv (b : GL (Fin n) E)
    ext x i
    simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

end Groups

section Levels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ)

theorem ratHom_bijective : Function.Bijective (ratHom hc n) := by
  constructor
  · intro a b hab
    have h1 : Formalism.UG.glEquiv (a : GL (Fin n) E) = Formalism.UG.glEquiv (b : GL (Fin n) E) := congrArg Subtype.val hab
    have h2 : (a : GL (Fin n) E) = b := by
      simpa [Formalism.UG.glEquiv] using h1
    exact Subtype.ext h2
  · intro u
    let g : GL (Fin n) E := Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm (u : Sp E n ≃ₗ[E] Sp E n))
    have hg : Formalism.UG.glEquiv g = (u : Sp E n ≃ₗ[E] Sp E n) := by
      simp [g, Formalism.UG.glEquiv]
    have h := (Formalism.UG.Final.HermBridge E (Fin n) (hStd E n) g).2
    rw [ad_gram_hStd, hg] at h
    have hm : g ∈ URat hc n := h u.2
    exact ⟨⟨g, hm⟩, Subtype.ext hg⟩

def ratEquiv : URat hc n ≃* UF E n := MulEquiv.ofBijective (ratHom hc n) (ratHom_bijective hc n)

def ratIn : URat hc n →* UAd hc n where
  toFun γ := (Formalism.L2.DIV.ratEl γ : UAd hc n)
  map_one' := Subtype.ext (map_one (Formalism.UG.bc (n := Fin n) (iA F E)))
  map_mul' a b := Subtype.ext (map_mul (Formalism.UG.bc (n := Fin n) (iA F E)) (a : GL (Fin n) E) b)

theorem ratIn_val (γ : URat hc n) :
    ((ratIn hc n γ : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) := rfl

variable [NeZero n] (ST SG : Finset (Pl E))

def mirAt (P : Pl E) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  ((mirab (kP P) n).comap (redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P)).map
    (St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).subtype

def J0 : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  UAd hc n ⊓ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⊓ ⨅ P ∈ ST, mirAt (F := F) n P

theorem congruence_le_adelic_unitary : J0 hc n ST ≤ UAd hc n := by
  unfold J0
  exact le_trans inf_le_left inf_le_left

theorem congruence_subgroup_le_stabilizer : J0 hc n ST ≤ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  unfold J0
  exact le_trans inf_le_left inf_le_right

def redG : J0 hc n ST →* GLG E n SG :=
  MonoidHom.pi fun w : SG =>
    (redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1).comp (Subgroup.inclusion (congruence_subgroup_le_stabilizer hc n ST))

def K1 : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := (redG hc n ST SG).ker.map (J0 hc n ST).subtype

theorem principal_le_congruence_subgroup : K1 hc n ST SG ≤ J0 hc n ST := by
  intro x hx
  unfold K1 at hx
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
  exact y.2

theorem principal_le_adelic_unitary : K1 hc n ST SG ≤ UAd hc n :=
  le_trans (principal_le_congruence_subgroup hc n ST SG) (congruence_le_adelic_unitary hc n ST)

abbrev adPt : Type := UAd hc n ⧸ (K1 hc n ST SG).subgroupOf (UAd hc n)

def ToUnitaryAdelic : J0 hc n ST →* UAd hc n := Subgroup.inclusion (congruence_le_adelic_unitary hc n ST)

theorem mem_principal_congruence_of {m : J0 hc n ST} (hm : redG hc n ST SG m = 1) :
    ToUnitaryAdelic hc n ST m ∈ (K1 hc n ST SG).subgroupOf (UAd hc n) := by
  rw [Subgroup.mem_subgroupOf]
  unfold K1
  exact Subgroup.mem_map.2 ⟨m, (MonoidHom.mem_ker).2 hm, rfl⟩

theorem K1_conj (k : J0 hc n ST) {a : UAd hc n} (ha : a ∈ (K1 hc n ST SG).subgroupOf (UAd hc n)) :
    ToUnitaryAdelic hc n ST k * a * (ToUnitaryAdelic hc n ST k)⁻¹ ∈ (K1 hc n ST SG).subgroupOf (UAd hc n) := by
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  unfold K1 at ha ⊢
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 ha
  refine Subgroup.mem_map.2 ⟨k * y * k⁻¹, (redG hc n ST SG).normal_ker.conj_mem y hy k, ?_⟩
  have hya' : (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = (a : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hya
  show (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (a : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹
  rw [hya']

variable (H : Subgroup (GLG E n SG))

abbrev JH : Subgroup (J0 hc n ST) := H.comap (redG hc n ST SG)

def redH : JH hc n ST SG H →* H :=
  ((redG hc n ST SG).comp (JH hc n ST SG H).subtype).codRestrict H (fun x => x.2)

def AdG : Type := URat hc n × (JH hc n ST SG H ⧸ (redH hc n ST SG H).ker)

instance : Group (AdG hc n ST SG H) := inferInstanceAs (Group (URat hc n × (JH hc n ST SG H ⧸ (redH hc n ST SG H).ker)))

def adHom : AdG hc n ST SG H →* UF E n × H :=
  show URat hc n × (JH hc n ST SG H ⧸ (redH hc n ST SG H).ker) →* UF E n × H from MonoidHom.prodMap (ratHom hc n) (QuotientGroup.kerLift (redH hc n ST SG H))

theorem adHom_mk (γ : URat hc n) (k : JH hc n ST SG H) :
    adHom hc n ST SG H ((γ, (k : JH hc n ST SG H ⧸ (redH hc n ST SG H).ker)) : AdG hc n ST SG H) =
      (ratHom hc n γ, redH hc n ST SG H k) := rfl

def rawSm (γ : URat hc n) (k : J0 hc n ST) (x : UAd hc n) : UAd hc n :=
  ratIn hc n γ * x * (ToUnitaryAdelic hc n ST k)⁻¹

theorem rawSm_wd (γ : URat hc n) (k₁ k₂ : JH hc n ST SG H) (x₁ x₂ : UAd hc n)
    (hk : k₁⁻¹ * k₂ ∈ (redH hc n ST SG H).ker) (hx : x₁⁻¹ * x₂ ∈ (K1 hc n ST SG).subgroupOf (UAd hc n)) :
    (rawSm hc n ST γ k₁.1 x₁)⁻¹ * rawSm hc n ST γ k₂.1 x₂ ∈ (K1 hc n ST SG).subgroupOf (UAd hc n) := by
  have hm : redG hc n ST SG ((k₁⁻¹ * k₂ : JH hc n ST SG H) : J0 hc n ST) = 1 :=
    congrArg Subtype.val ((MonoidHom.mem_ker).1 hk)
  have hu := mem_principal_congruence_of hc n ST SG hm
  have hc' := K1_conj hc n ST SG k₁.1 (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hu))
  convert hc' using 1
  simp only [rawSm, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  group

def adSmul (g : URat hc n × (JH hc n ST SG H ⧸ (redH hc n ST SG H).ker)) (q : adPt hc n ST SG) :
    adPt hc n ST SG :=
  Quotient.liftOn₂' g.2 q (fun k x => (rawSm hc n ST g.1 k.1 x : adPt hc n ST SG)) (by
    intro k₁ x₁ k₂ x₂ hk hx
    exact QuotientGroup.eq.2 (rawSm_wd hc n ST SG H g.1 k₁ k₂ x₁ x₂
      (QuotientGroup.leftRel_apply.1 hk) (QuotientGroup.leftRel_apply.1 hx)))

theorem adSmul_mk (γ : URat hc n) (k : JH hc n ST SG H) (x : UAd hc n) :
    adSmul hc n ST SG H (γ, (k : JH hc n ST SG H ⧸ (redH hc n ST SG H).ker)) (x : adPt hc n ST SG) =
      (rawSm hc n ST γ k.1 x : adPt hc n ST SG) := rfl

instance (priority := high) adAct : MulAction (AdG hc n ST SG H) (adPt hc n ST SG) where
  smul := adSmul hc n ST SG H
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      show adSmul hc n ST SG H (1, ((1 : JH hc n ST SG H) : JH hc n ST SG H ⧸ _)) (x : adPt hc n ST SG) = x
      rw [adSmul_mk]
      congr 1
      simp [rawSm]
  mul_smul g g' q := by
    obtain ⟨γ, k⟩ := g
    obtain ⟨γ', k'⟩ := g'
    induction k using QuotientGroup.induction_on with
    | H k =>
    induction k' using QuotientGroup.induction_on with
    | H k' =>
    induction q using QuotientGroup.induction_on with
    | H x =>
      show adSmul hc n ST SG H (γ * γ', ((k * k' : JH hc n ST SG H) : JH hc n ST SG H ⧸ _)) (x : adPt hc n ST SG) =
        adSmul hc n ST SG H (γ, (k : JH hc n ST SG H ⧸ _)) (adSmul hc n ST SG H (γ', (k' : JH hc n ST SG H ⧸ _)) x)
      rw [adSmul_mk, adSmul_mk, adSmul_mk]
      congr 1
      simp only [rawSm, map_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
      group

end Levels

section DecoOf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

def decoRaw (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Deco E n ST SG where
  N := Formalism.UG.CS.globLat x (stdLat E n)
  f P v := open Classical in
    if v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then redA P.1 (pullV x v (lastIdx n)) else 0
  be w v := open Classical in
    if v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then fun i => redA w.1 (pullV x v i) else 0

def decoOf (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : DecoSet E n ST SG :=
  open Classical in if h : (decoRaw ST SG x).Ok then ⟨_, h⟩ else DecoSet.base E n ST SG

end DecoOf

section DecoPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

def decoPt (q : adPt hc n ST SG) : DecoSet E n ST SG :=
  decoOf ST SG ((Quotient.out q : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

end DecoPt

section Iso

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def pullGSD (S : GSD K) (G' D' : Type) [Group G'] [MulAction G' D'] (φ : G' →* S.G) (p : D' → S.D) : GSD K where
  G := G'
  D := D'
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ.comp φ
  Nab := S.Nab ∘ p
  Del := S.Del ∘ p

theorem repr_self_mem (S : GSD K) (i j : S.ιV) : S.bV.repr (S.bV j) i ∈ Formalism.DivisionValues.cmMax K := by
  rw [S.bV.repr_self, Finsupp.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def pullIso (S : GSD K) (G' D' : Type) [Group G'] [MulAction G' D'] (φ : G' →* S.G) (p : D' → S.D)
    (hφ : Function.Bijective φ) (hp : Function.Bijective p) (heq : ∀ (g : G') (d : D'), p (g • d) = φ g • p d) :
    GSD.Iso (pullGSD S G' D' φ p) S where
  eG := MulEquiv.ofBijective φ hφ
  eD := Equiv.ofBijective p hp
  eV := LinearEquiv.refl K S.V
  smul := heq
  rho _ _ := rfl
  pair _ _ := rfl
  nab _ := (Submodule.map_id _).symm
  del _ := (Submodule.map_id _).symm
  rat i j := repr_self_mem S i j
  rat_symm i j := repr_self_mem S i j

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

instance decoActH : MulAction (UF E n × H) (DecoSet E n ST SG) :=
  MulAction.compHom _ (MonoidHom.prodMap (MonoidHom.id (UF E n)) H.subtype)

structure OnDeco (S : GSD K) where
  eG : (UF E n × H) ≃* S.G
  eD : DecoSet E n ST SG ≃ S.D
  smul : ∀ (g : UF E n × H) (d : DecoSet E n ST SG), eD (g • d) = eG g • eD d

variable {hc n ST SG H}

def adGSD (hc : Formalism.BasicNotions.CMData F E) {S : GSD K} (o : OnDeco n ST SG H S) : GSD K :=
  pullGSD S (AdG hc n ST SG H) (adPt hc n ST SG) (o.eG.toMonoidHom.comp (adHom hc n ST SG H)) (o.eD ∘ decoPt hc n ST SG)

variable (hc n ST SG H)

def DecoOfOk : Prop := ∀ x ∈ UAd hc n, (decoRaw ST SG x).Ok

def DecoPtBij : Prop := Function.Bijective (decoPt hc n ST SG)

def DecoPtEqv : Prop :=
  ∀ (g : AdG hc n ST SG H) (q : adPt hc n ST SG), decoPt hc n ST SG (adSmul hc n ST SG H g q) = adHom hc n ST SG H g • decoPt hc n ST SG q

def RedHSurj : Prop := Function.Surjective (redH hc n ST SG H)

theorem adHom_bijective (hR : RedHSurj hc n ST SG H) : Function.Bijective (adHom hc n ST SG H) := by
  have h1 := ratHom_bijective hc n
  have h2 : Function.Bijective (QuotientGroup.kerLift (redH hc n ST SG H)) := by
    refine ⟨QuotientGroup.kerLift_injective _, fun h => ?_⟩
    obtain ⟨k, rfl⟩ := hR h
    exact ⟨(k : JH hc n ST SG H ⧸ (redH hc n ST SG H).ker), rfl⟩
  show Function.Bijective (Prod.map (ratHom hc n) (QuotientGroup.kerLift (redH hc n ST SG H)))
  exact ⟨h1.1.prodMap h2.1, h1.2.prodMap h2.2⟩

def adelicIso {S : GSD K} (o : OnDeco n ST SG H S) (hB : DecoPtBij hc n ST SG) (hE : DecoPtEqv hc n ST SG H)
    (hR : RedHSurj hc n ST SG H) : GSD.Iso (adGSD hc o) S :=
  pullIso S _ _ _ _ (o.eG.bijective.comp (adHom_bijective hc n ST SG H hR)) (o.eD.bijective.comp hB) (by
    intro g q
    show o.eD (decoPt hc n ST SG (adSmul hc n ST SG H g q)) = o.eG (adHom hc n ST SG H g) • o.eD (decoPt hc n ST SG q)
    rw [hE, o.smul])

end Iso

end Formalism.L2.Col
