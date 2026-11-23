import Formalism.LocalToGlobal.Columns.RecLevelStep
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.Columns.TwQDefs
import Formalism.LocalToGlobal.Columns.TwQThetaOpen

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn underPl)
open Formalism.UG

section QLev

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {Θ : LevQFam E K n Q}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

abbrev qFst (q : QLoc hc n Q Θ) (P : Q) : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F) →* GL (Fin n) ((qv F P.1).adicCompletion F) :=
  bc ((RingHom.fst _ _).comp (q.sp P).toRingHom)

structure QOpen (q : QLoc hc n Q Θ) : Prop where
  princ : ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) (qv F P.1) (stdLat E n),
    (∀ y ∈ Formalism.L2.Herm.locL (qv F P.1) (stdLat E n), ∃ z ∈ Formalism.L2.Herm.locL (qv F P.1) (stdLat E n),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F)) *ᵥ y - y =
        (N : E ⊗[F] (qv F P.1).adicCompletion F) • z) → qFst q P x ∈ q.U P
  glob : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ u ∈ UAd hc n, ∀ s : Fin n → Fin n → Formalism.L2.Herm.intAf F E,
    (∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j = (1 : Matrix (Fin n) (Fin n) 𝒜) i j + iA F E (algebraMap (𝓞 E) E a) * s i j) →
    ∀ P : Q, q.at P u ∈ q.U P

variable (q : QLoc hc n Q Θ) (H : Subgroup (GLG E n SG))

theorem mem_levUQ {x : GL (Fin n) 𝒜} :
    x ∈ levUQ hc n ST SG Q H q ↔ x ∈ levU hc n ST SG H ∧ ∀ P : Q, q.at P x ∈ q.U P := by
  unfold levUQ
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

theorem levUQ_le : levUQ hc n ST SG Q H q ≤ levU hc n ST SG H := inf_le_left

def lqRes (P : Q) : levUQ hc n ST SG Q H q →* q.U P where
  toFun x := ⟨q.at P x.1, ((mem_levUQ q H).1 x.2).2 P⟩
  map_one' := by
    ext1
    show q.at P 1 = 1
    simp only [QLoc.at, map_one]
  map_mul' a b := by
    ext1
    show q.at P (a.1 * b.1) = q.at P a.1 * q.at P b.1
    simp only [QLoc.at, map_mul]

def chiQ (σ₀ : K →+* ℂ) : levUQ hc n ST SG Q H q →* ℂˣ :=
  ∏ P : Q, (Units.map σ₀.toMonoidHom).comp ((q.chr P).comp (lqRes q H P))

variable (ST) in

def qUloc (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)) :=
  levLoc hc n ST SG H v ⊓ ⨅ (P : Q) (h : qv F P.1 = v), h ▸ (q.U P).comap (qFst q P)

theorem mem_qUloc (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    x ∈ qUloc ST q H v ↔ x ∈ levLoc hc n ST SG H v ∧ ∀ (P : Q) (h : qv F P.1 = v), x ∈ h ▸ (q.U P).comap (qFst q P) := by
  unfold qUloc
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf]

section Top

attribute [local instance] rlt_top rlt_topRing adeles_t2Space

theorem lq_open (hQ : QOpen q) : IsOpen {x : UAd hc n | (x : GL (Fin n) 𝒜) ∈ levUQ hc n ST SG Q H q} := by
  classical
  obtain ⟨a1, ha10, ha1⟩ := hQ.glob
  obtain ⟨a0, ha00, ha0⟩ := rlt_exists_a (ST ∪ SG)
  set a : 𝓞 E := a1 * a0 with ha_def
  have ha0' : (algebraMap (𝓞 E) E a) ≠ 0 := by
    rw [ha_def, map_mul]
    exact mul_ne_zero (by simpa using ha10) (by simpa using ha00)
  set c : 𝒜 := iA F E (algebraMap (𝓞 E) E a)⁻¹ with hc'
  have hca : iA F E (algebraMap (𝓞 E) E a) * c = 1 := by
    rw [hc', ← map_mul, mul_inv_cancel₀ ha0', map_one]
  let W : Set (GL (Fin n) 𝒜) := {u | ∀ i j, c * ((u : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j) ∈
    Formalism.L2.Herm.intAf F E}
  have hWo : IsOpen W := by
    have : W = ⋂ i, ⋂ j, (fun u : GL (Fin n) 𝒜 => c * ((u : Matrix (Fin n) (Fin n) 𝒜) i j - (1 : Matrix (Fin n) (Fin n) 𝒜) i j)) ⁻¹'
        (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
      ext u; simp [W]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => rlt_isOpen_intAf.preimage ?_
    exact continuous_const.mul ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  have hW1 : (1 : GL (Fin n) 𝒜) ∈ W := by
    intro i j
    simp
  have hsub : ∀ u ∈ UAd hc n, u ∈ W → u ∈ levUQ hc n ST SG Q H q := by
    intro u hu hW
    have hs : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝒜) i j =
        (1 : Matrix (Fin n) (Fin n) 𝒜) i j + iA F E (algebraMap (𝓞 E) E a) * (⟨_, hW i j⟩ : Formalism.L2.Herm.intAf F E) := by
      intro i j
      show _ = _ + iA F E (algebraMap (𝓞 E) E a) * (c * _)
      rw [← mul_assoc, hca, one_mul]
      ring
    refine (mem_levUQ q H).2 ⟨kOne_le_unipotentLevel hc n ST SG H (mem_kOne_of_congruent_one hc n ST SG a
      (fun P hP => Ideal.mul_mem_left _ _ (ha0 P (Finset.mem_union_left _ hP)))
      (fun P hP => Ideal.mul_mem_left _ _ (ha0 P (Finset.mem_union_right _ hP))) hu (fun i j => ⟨_, hW i j⟩) hs), ?_⟩
    refine ha1 u hu (fun i j => Formalism.L2.DIV.oToS F E a0 * ⟨_, hW i j⟩) (fun i j => ?_)
    refine (hs i j).trans ?_
    have e : (iA F E (algebraMap (𝓞 E) E a) : 𝒜) =
        iA F E (algebraMap (𝓞 E) E a1) * ((Formalism.L2.DIV.oToS F E a0 : Formalism.L2.Herm.intAf F E) : 𝒜) := by
      rw [ha_def, map_mul, map_mul]
      rfl
    show _ = _ + _ * (((Formalism.L2.DIV.oToS F E a0 : Formalism.L2.Herm.intAf F E) : 𝒜) * _)
    rw [e, mul_assoc]
  have hnh : (((levUQ hc n ST SG Q H q).subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) ∈ nhds (1 : UAd hc n) := by
    refine Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hW1) ?_
    intro x hx
    exact hsub x.1 x.2 hx
  exact Subgroup.isOpen_of_mem_nhds _ hnh

theorem lq_compact (hQ : QOpen q) : IsCompact (levUQ hc n ST SG Q H q : Set (GL (Fin n) 𝒜)) := by
  have hcl : IsClosed (((levUQ hc n ST SG Q H q).subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) :=
    Subgroup.isClosed_of_isOpen _ (lq_open q H hQ)
  have hUA : levUQ hc n ST SG Q H q ≤ UAd hc n := (levUQ_le q H).trans (levU_le_UAd hc n ST SG H)
  have himg : (levUQ hc n ST SG Q H q : Set (GL (Fin n) 𝒜)) =
      Subtype.val '' (((levUQ hc n ST SG Q H q).subgroupOf (UAd hc n) : Subgroup (UAd hc n)) : Set (UAd hc n)) := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u, hUA hu⟩, hu, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hclosed : IsClosed (levUQ hc n ST SG Q H q : Set (GL (Fin n) 𝒜)) := by
    rw [himg]
    exact (rlt_isClosed_UAd hc n).isClosedEmbedding_subtypeVal.isClosedMap _ hcl
  exact (levU_compact hc n ST SG H).of_isClosed_subset hclosed (levUQ_le q H)

end Top

section Step

variable {π : 𝓞 E} {T f : ℕ} (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))

def badQ' (SG Q : Finset (Pl E)) : Set (HeightOneSpectrum (𝓞 F)) := plUnder F SG ∪ {v | ∃ P : Q, qv F P.1 = v}

variable (q : QLoc hc n Q Θ)

theorem qUloc_of_not (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ P : Q, qv F P.1 ≠ v) :
    qUloc ST q (Subgroup.pi Set.univ Hw) v = levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v := by
  apply le_antisymm
  · intro x hx
    exact ((mem_qUloc q _ v x).1 hx).1
  · intro x hx
    exact (mem_qUloc q _ v x).2 ⟨hx, fun P h => absurd h (hv P)⟩

theorem levUQ_eq_prod (x : GL (Fin n) 𝒜) :
    x ∈ levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q ↔
      x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) ∧
        ∀ v, bc (prV (E := E) v) x ∈ qUloc ST q (Subgroup.pi Set.univ Hw) v := by
  rw [mem_levUQ, levU_eq_prod hc n ST SG Hw x]
  constructor
  · rintro ⟨⟨hU, hloc⟩, hQ⟩
    refine ⟨hU, fun v => (mem_qUloc q _ v _).2 ⟨hloc v, fun P h => ?_⟩⟩
    subst h
    exact hQ P
  · rintro ⟨hU, hloc⟩
    refine ⟨⟨hU, fun v => ((mem_qUloc q _ v _).1 (hloc v)).1⟩, fun P => ?_⟩
    exact ((mem_qUloc q _ _ _).1 (hloc (qv F P.1))).2 P rfl

variable (hc n)

def stepOfQ (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ)
    (hQ : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) :
    Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f (badQ' SG Q) where
  Lb := baseLb E n ST
  Lb_fin := baseLb_fin n ST
  Lb_span := baseLb_span n ST
  Lb_int := baseLb_int hc n ST
  Lb_dual := baseLb_dual hc n ST (fun P hP => (hST P).1 hP) hTπ
  Lb_index := hidx
  Uloc := qUloc ST q (Subgroup.pi Set.univ Hw)
  Uloc_le v := le_trans inf_le_left (levLoc_le hc n ST SG _ v)
  Uloc_lev v := le_trans inf_le_left (levLoc_le_levelVL hc n ST SG _ v)
  Uloc_hyp v hv hT := by
    rw [qUloc_of_not Hw q v (fun P h => hv (Or.inr ⟨P, h⟩))]
    exact levLoc_eq_levelVL hc n ST SG _ v
      (fun h => hT ((mem_plUnder_iff_norm hc hST T hTπ v).1 h)) (fun h => hv (Or.inl h))
  fM v _ := fMod hc n ST v
  fT v _ := fLoc hc n ST v
  fT_ne v h := fLoc_ne hc n v hB ((mem_plUnder_iff_norm hc hST T hTπ v).2 h)
  fT_T v _ x := fLoc_natCast_smul_eq_zero_of_dvd hc n v hB T ⟨cO E π, hTπ.symm⟩ x
  fM_card v h := by
    obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    rw [fMod_card hc n v hB hP hov (hB.over_unique hc hP hov), hcard P hP]
  fT_L v _ x hx := fLoc_L hc n v x hx
  UlocAlt v h := by
    rw [qUloc_of_not Hw q v (fun P hP => hQT P (hP ▸ h))]
    exact levLoc_eq_stabFun hc n SG _ v hB (hSG v h)
  U := levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q
  U_eq x := levUQ_eq_prod Hw q x
  U_compact := lq_compact q _ hQ
  U_open := lq_open q _ hQ
  chi := (levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹
  chi_triv x h := by
    have h1 : levTyp lam (Subgroup.inclusion (levUQ_le q _) x) = 1 :=
      levTyp_eq_one hc n ST SG _ lam _ fun v hv => h v (Or.inl hv)
    have h2 : chiQ q _ σ₀ x = 1 := by
      unfold chiQ
      rw [MonoidHom.finsetProd_apply]
      refine Finset.prod_eq_one fun P _ => ?_
      have hx : lqRes q (Subgroup.pi Set.univ Hw) P x = 1 := by
        ext1
        show q.at P x.1 = 1
        simp only [QLoc.at]
        rw [h (qv F P.1) (Or.inr ⟨P, rfl⟩), map_one]
      simp only [MonoidHom.comp_apply, hx, map_one]
    show levTyp lam (Subgroup.inclusion (levUQ_le q _) x) * (chiQ q _ σ₀ x)⁻¹ = 1
    rw [h1, h2, inv_one, one_mul]

theorem chiQ_pow_eq_one (σ₀ : K →+* ℂ) (x : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q) (m2 : Q → ℕ)
    (h2 : ∀ (P : Q) (k : q.U P), q.chr P k ^ m2 P = 1) (M : ℕ) (hM : ∀ P : Q, m2 P ∣ M) : chiQ q _ σ₀ x ^ M = 1 := by
  unfold chiQ
  rw [MonoidHom.finsetProd_apply, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun P _ => ?_
  obtain ⟨M', hM'⟩ := hM P
  rw [hM', pow_mul, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_pow, h2, map_one, one_pow]

theorem chiQ_eq_one_of (σ₀ : K →+* ℂ) (x : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q)
    (h1 : ∀ P : Q, bc (prV (E := E) (qv F P.1)) x.1 = 1) : chiQ q _ σ₀ x = 1 := by
  unfold chiQ
  rw [MonoidHom.finsetProd_apply]
  refine Finset.prod_eq_one fun P _ => ?_
  have hx : lqRes q (Subgroup.pi Set.univ Hw) P x = 1 := by
    ext1
    show q.at P x.1 = 1
    simp only [QLoc.at]
    rw [h1 P, map_one]
  simp only [MonoidHom.comp_apply, hx, map_one]

theorem stepOfQ_chi_fin (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ)
    (hQ : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ)
    (hlam : ∃ m : ℕ, 0 < m ∧ ∀ h, lam h ^ m = 1) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ κ, (stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hQ hQT σ₀).chi κ ^ m = 1 := by
  classical
  obtain ⟨m1, hm1, h1⟩ := hlam
  choose m2 hm2 h2 using hchr
  refine ⟨m1 * ∏ P : Q, m2 P, Nat.mul_pos hm1 (Finset.prod_pos fun P _ => hm2 P), fun κ => ?_⟩
  show ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) κ * (chiQ q _ σ₀ κ)⁻¹) ^ _ = 1
  rw [mul_pow, inv_pow]
  have ha : ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) κ) ^ (m1 * ∏ P : Q, m2 P) = 1 := by
    show ((lam (levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) κ)))⁻¹) ^ _ = 1
    rw [inv_pow, pow_mul, h1, one_pow, inv_one]
  have hb : (chiQ q _ σ₀ κ) ^ (m1 * ∏ P : Q, m2 P) = 1 :=
    chiQ_pow_eq_one hc n Hw q σ₀ (κ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q) m2 h2 _
      (fun P => Dvd.dvd.mul_left (Finset.dvd_prod_of_mem m2 (Finset.mem_univ P)) _)
  rw [ha, hb, inv_one, one_mul]

theorem stepOfQ_chi_off (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ)
    (hQ : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ)
    (κ : (stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hQ hQT σ₀).U) (κ' : (stepOf hc n Hw hB hTπ hST hcard hSG hidx lam).U)
    (he : κ.1 = κ'.1) (h1 : ∀ P : Q, bc (prV (E := E) (qv F P.1)) κ.1 = 1) :
    (stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hQ hQT σ₀).chi κ = (stepOf hc n Hw hB hTπ hST hcard hSG hidx lam).chi κ' := by
  have h2 : chiQ q _ σ₀ κ = 1 := chiQ_eq_one_of hc n Hw q σ₀ (κ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q) h1
  show levTyp lam (Subgroup.inclusion (levUQ_le q _) κ) * (chiQ q _ σ₀ κ)⁻¹ = levTyp lam κ'
  rw [h2, inv_one, mul_one]
  congr 1
  exact Subtype.ext he

end Step

end QLev

end Formalism.L2.Col
