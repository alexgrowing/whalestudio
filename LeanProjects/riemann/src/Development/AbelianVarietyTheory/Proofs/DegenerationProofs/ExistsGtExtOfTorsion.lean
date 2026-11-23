import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcExt
open GlobalTheory.TorusExt

section Val
variable {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem epi_spMap : Epi (spMap f) := by
  have : Flat (spMap f) := inferInstance
  have : Surjective (spMap f) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem valF_ext (t : Sp F ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF (spMap f ≫ t) U a = f (valF t U a) := by
  have h' : ⊤ ≤ (spMap f ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap f q))
  rw [valF, dif_pos h', valF, dif_pos ht]
  have e : (spMap f ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom f := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap f) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

theorem top_le_chart {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (φ : K → (Y ⟶ X))
    (r : Sp F ⟶ Y) : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun z _ =>
  Good.mem (L := L) (z := z) (J := J) (fun ψ => hJ ψ trivial) φ r

theorem vF_ne_zero {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) : vF t r J ≠ 0 := by
  refine fun h => ?_
  exact (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (top_le_chart hJ φ r)).symm.trans h)

theorem val_eq_vF {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (y : Sp F) : (val t r y J).val = stalkConst y (vF t r J) :=
  (gs_unit r y _ (top_le_chart hJ φ r trivial) _).symm.trans (gs_eq_stalkConst r y (top_le_chart hJ φ r) _)

theorem exists_gauge (hL : L.IsLB) {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) :
    ∃ J' : (Sp F' ⟶ X) → L.ι, (∀ ψ : Sp F' ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ)) ∧ ∀ ψ, J' (spMap f ≫ ψ) = J ψ := by
  have := epi_spMap f
  let y : Sp F' := IsLocalRing.closedPoint F'
  obtain ⟨J', h, e⟩ := exists_good L hL y (fun ψ : Sp F ⟶ X => spMap f ≫ ψ) J
    (fun a b e => congrArg J ((cancel_epi _).1 e)) fun ψ => hJ ψ (Set.mem_univ (spMap f y))
  exact ⟨J', fun ψ z _ => (Subsingleton.elim (α := PrimeSpectrum F') y z) ▸ h ψ, e⟩

variable {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {J' : (Sp F' ⟶ X) → L.ι}
  (hJ' : ∀ ψ, J' (spMap f ≫ ψ) = J ψ) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
include hJ hJ'

theorem vF_ext (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) : vF t (spMap f ≫ r) J' = f (vF t r J) := by
  have e : (fun k => J' ((spMap f ≫ r) ≫ φ k)) = fun k => J (r ≫ φ k) := funext fun k => by
    rw [Category.assoc, hJ']
  have k : ∀ j j' : K → L.ι, j = j' → valF (spMap f ≫ r) (LB.wchart L φ j) (t.s j).val =
      valF (spMap f ≫ r) (LB.wchart L φ j') (t.s j').val := by rintro _ _ rfl; rfl
  exact (k _ _ e).trans (valF_ext f r _ (top_le_chart hJ φ r) _)

theorem sF_ext (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) : sF s (spMap f ≫ r) J' = f (sF s r J) := by
  have e : (fun k => J' ((spMap f ≫ r) ≫ φ k)) = fun k => J (r ≫ φ k) := funext fun k => by
    rw [Category.assoc, hJ']
  have k : ∀ j j' : K → L.ι, j = j' → valF (spMap f ≫ r) (LB.wchart L φ j) (s.f j) =
      valF (spMap f ≫ r) (LB.wchart L φ j') (s.f j') := by rintro _ _ rfl; rfl
  exact (k _ _ e).trans (valF_ext f r _ (top_le_chart hJ φ r) _)

end Val

theorem card_torsion (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ S)
    {n : ℕ} (hn : (n : k) ≠ 0) : Nat.card {x : Over.mk t ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hL.polBaseChange S _ t P
  rw [← hdim, ← (hL.mulN _ P' n (Nat.pos_of_ne_zero hn0)).2.2.2.2 k (𝟙 _) hn]
  let ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  let Φ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P'.A) →* (Over.mk t ⟶ P.A) :=
    MonoidHom.mk' (fun x => ρ ≫ toBase hg.w x) fun x y => by rw [hmul, MonObj.comp_mul]
  have hΦ : ∀ x, (Φ x).left = x.left ≫ g := fun x => Category.id_comp _
  have hb : Function.Bijective Φ := by
    refine ⟨fun x y e => Over.OverMorphism.ext (hg.hom_ext ?_ ((Over.w x).trans (Over.w y).symm)), fun a => ?_⟩
    · rw [← hΦ, ← hΦ, e]
    · exact ⟨Over.homMk (hg.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp t).symm)) (hg.lift_snd _ _ _),
        Over.OverMorphism.ext ((hΦ _).trans (hg.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective Φ hb
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    show _ ↔ e x ^ n = 1
    rw [← map_pow, EmbeddingLike.map_eq_one_iff])).symm

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem card_gt_torsion (hL : Laws) (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    {n : ℕ} (hn : (n : F) ≠ 0) : Nat.card {g : GtPtF D F // n • g = 0} = n ^ (2 * D.P.g) * n ^ D.rank := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  rw [← GtCount.card_torsion_over_zero D F n hn, ← card_torsion hL D.P (TF (R := R) F).hom hn]
  exact GtCount.card_torsion_eq_mul (gtProj D F) n fun b hb =>
    exists_nsmul_eq_of_pow_eq hn0 0 (b := b.toMul) (Eq.trans hb zero_b.symm)

theorem vF_gtExt {J : (Sp F ⟶ D.P.A.left) → D.P.L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ))
    {J' : (Sp F' ⟶ D.P.A.left) → D.P.L.ι} (hg : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J' ψ)) (hJ' : ∀ ψ, J' (spMap f ≫ ψ) = J ψ)
    (g : GtPtF D F) (χ : D.X) : vF ((gtExt D f hf g).s χ) (𝟙 (Sp F')) J' = f (vF (g.s χ) (𝟙 (Sp F)) J) := by
  let y : Sp F' := IsLocalRing.closedPoint F'
  rw [← vF_ext f hJ hJ', Category.comp_id]
  refine (stalkConst y).injective ((val_eq_vF hg _ _ y).symm.trans (Eq.trans ?_ (val_eq_vF hg _ _ y)))
  exact congrArg Units.val (gtExt_val f hf g χ (y := y) (J := J') fun ψ => hg ψ trivial)

theorem gtExt_injective : Function.Injective (gtExt D f hf) := fun g g' e => by
  have := epi_spMap f
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  have hJ₁ : ∀ ψ : Sp F ⟶ D.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => pt_eq (R := R) y z ▸ hJ ψ
  obtain ⟨J', hg, hJ'⟩ := exists_gauge f D.P.isLB hJ₁
  have hb := congrArg (fun h : GtPtF D F' => h.b.left) e
  simp only [gtExt_b, Over.comp_left, extMap_left] at hb
  refine gt_ext_val_at (Over.OverMorphism.ext ((cancel_epi (spMap f)).1 hb)) hJ fun χ => Units.ext ?_
  refine (val_eq_vF hJ₁ _ _ y).trans (Eq.trans (congrArg _ (f.injective ?_)) (val_eq_vF hJ₁ _ _ y).symm)
  exact (vF_gtExt f hf hJ₁ hg hJ' g χ).symm.trans
    ((congrArg (fun h : GtPtF D F' => vF (h.s χ) (𝟙 (Sp F')) J') e).trans (vF_gtExt f hf hJ₁ hg hJ' g' χ))

theorem exists_gtExt_of_torsion (hL : Laws) [IsAlgClosed F] [IsAlgClosed F'] {n : ℕ} (hn : (n : F) ≠ 0)
    (g' : GtPtF D F') (h : n • g' = 0) : ∃ g, gtExt D f hf g = g' := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hn' : (n : F') ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hn
  let u : {g : GtPtF D F // n • g = 0} → {g : GtPtF D F' // n • g = 0} := fun g =>
    ⟨gtExt D f hf g.1, by rw [← map_nsmul, g.2, map_zero]⟩
  have hu : Function.Injective u := fun a b e => Subtype.ext (gtExt_injective f hf (congrArg Subtype.val e))
  have c := card_gt_torsion hL D F hn
  have c' := card_gt_torsion hL D F' hn'
  have : Finite {g : GtPtF D F' // n • g = 0} := Nat.finite_of_card_ne_zero (by rw [c']; positivity)
  obtain ⟨g, e⟩ := (hu.bijective_of_nat_card_le (c'.trans c.symm).le).2 ⟨g', h⟩
  exact ⟨g.1, congrArg Subtype.val e⟩

variable (hB : D.TauBimult) {k : ℕ}

theorem equiv_qkExt_iff (p q : QkPt D F k) :
    QkPt.Equiv D F' (qkExt hB f hf p) (qkExt hB f hf q) ↔ QkPt.Equiv D F p q := by
  refine ⟨fun h => ?_, qkExt_congr hB f hf⟩
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  refine (equiv_iff hB _ _).2 ⟨z, hy, gtExt_injective f hf ?_⟩
  rw [map_add, gtExt_iota]
  exact hg

theorem exists_qkExt (hL : Laws) [IsAlgClosed F] [IsAlgClosed F'] (hk : (k : F) ≠ 0) (p' : QkPt D F' k) :
    ∃ p, qkExt hB f hf p = p' := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  obtain ⟨q, hq⟩ := exists_qkPt (F := F) hL.mulN (Or.inr hL.polBaseChange) hB hk0 p'.y
  obtain ⟨t, ht⟩ := exists_gtExt_of_torsion f hf hL hk (p'.g - gtExt D f hf q.g) (by
    rw [nsmul_sub, ← map_nsmul, qk_nsmul hB, qk_nsmul hB, gtExt_iota, hq, sub_self])
  have ht0 : k • t = 0 := gtExt_injective f hf (by
    rw [map_nsmul, ht, map_zero, nsmul_sub, ← map_nsmul, qk_nsmul hB, qk_nsmul hB, gtExt_iota, hq, sub_self])
  refine ⟨qkMk hB p'.y (q.g + t) (by rw [nsmul_add, ht0, add_zero, qk_nsmul hB, hq]), qk_ext rfl ?_⟩
  show gtExt D f hf (q.g + t) = _
  rw [map_add, ht, add_sub_cancel]

section Hom
variable {N : NumD F} {N' : NumD F'} (ν : NumOf D F N) (ν' : NumOf D F' N')
  (hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ) (hth : ν'.th = ν.th)

def ptHom : N.A →* N'.A :=
  MonoidHom.mk' (fun x => ν'.eA.symm (extMap f hf ≫ ν.eA x)) fun x y => by rw [map_mul, MonObj.comp_mul, map_mul]

theorem eA_ptHom (x : N.A) : ν'.eA (ptHom f hf ν ν' x) = extMap f hf ≫ ν.eA x := ν'.eA.apply_symm_apply _

def rigVal (ν : NumOf D F N) : F :=
  vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom ν.J

include hf hJ in
theorem rg_ext : rigVal ν' = f (rigVal ν) := by
  rw [rigVal, rigVal, ← vF_ext f ν.good hJ]
  exact congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r ν'.J)
    (Over.w (extMap (R := R) f hf)).symm

def numHom : NumD.Hom f N N' where
  φ := ptHom f hf ν ν'
  h _ := 1
  h_one := rfl
  θ_eq x y u := by
    simp only [_root_.mul_one]
    refine Units.ext ?_
    show _ = f (N.θ x y u : F)
    rw [ν'.θ_eq, ν.θ_eq, eA_ptHom, eA_ptHom, eA_ptHom, ← comp_lift, ← comp_lift]
    exact vF_ext f ν.good hJ _ _
  σ_eq x := by
    simp only [_root_.mul_one]
    refine Units.ext ?_
    show _ = f (N.σ x : F)
    rw [ν'.σ_eq, ν.σ_eq, ← vF_ext f ν.good hJ, eA_ptHom]
    rfl
  lam := 1
  th_eq x := by
    rw [_root_.mul_one, Units.val_one, _root_.one_mul]
    have h0 : rigVal ν' ≠ 0 := vF_ne_zero ν'.good _ _
    refine mul_right_cancel₀ h0 ((ν'.th_eq _).trans ?_)
    rw [rg_ext f hf ν ν' hJ, ← map_mul, rigVal, ν.th_eq, ← sF_ext f ν.good hJ, eA_ptHom, hth]
    rfl
  e := ν.eX.trans ν'.eX.symm
  c_eq χ := ν'.eA.injective (by
    rw [ν'.c_eq, eA_ptHom, ν.c_eq, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    exact (DVR.comp_cP D (extMap f hf) _).symm)
  ψ_eq χ := by
    simp only [_root_.mul_one]
    refine Units.ext ?_
    show _ = f (N.ψ χ : F)
    rw [ν'.ψ_eq, ν.ψ_eq, map_mul, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    refine congrArg₂ (· * ·) ?_ (rg_ext f hf ν ν' hJ)
    rw [← vF_ext f ν.good hJ]
    exact congrArg (fun r => vF (D.psi (ν.eX χ)) r ν'.J) ((extMap_jFK f hf).trans (Category.id_comp _)).symm

theorem eX_numHom (y : N.X) : ν'.eX ((numHom f hf ν ν' hJ hth).e y) = ν.eX y := ν'.eX.apply_symm_apply _

theorem numHom_rel {g : GtPtF D F} {c : N.Gt} {c' : N'.Gt} (h : ν.Pt g c) (h' : ν'.Pt (gtExt D f hf g) c') :
    (numHom f hf ν ν' hJ hth).Rel c c' := by
  refine ⟨ν'.eA.injective (h'.1.trans ?_), fun χ => ?_⟩
  · rw [gtExt_b, ← h.1]
    exact (eA_ptHom f hf ν ν' _).symm
  · show _ * 1 = _ * 1 * 1
    simp only [_root_.mul_one]
    refine Units.ext ?_
    show _ = f (c.s χ : F)
    rw [h'.2, h.2, eX_numHom]
    exact vF_gtExt f hf ν.good ν'.good hJ g _

theorem numHom_qPt {p : QkPt D F k} {q : N.QT k} {q' : N'.QT k} (h : ν.QPt p q) (h' : ν'.QPt (qkExt hB f hf p) q') :
    q'.1.1.toAdd = (numHom f hf ν ν' hJ hth).e q.1.1.toAdd ∧ (numHom f hf ν ν' hJ hth).Rel q.1.2 q'.1.2 :=
  ⟨ν'.eX.injective (h'.1.trans (h.1.symm.trans (eX_numHom f hf ν ν' hJ hth _).symm)),
    numHom_rel f hf ν ν' hJ hth h.2 h'.2⟩

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tateExt (hL : Laws) [IsAlgClosed F] [CharZero F] [IsAlgClosed F'] {Dt : Datum H} [Module (𝓞 E) D.X]
    {oa : letI := H.starRing; D.OAct (𝓞 E)} (I : TateIsoQ Dt D oa F)
    (hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt D F k) (z : F), WeilQkIs D F k p p' z →
      WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z)) : TateIsoQ Dt D oa F' where
  ζ n := Units.map f.toMonoidHom (I.ζ n)
  ζ_prim n hn := (I.ζ_prim n hn).map_of_injective (Units.map_injective f.injective)
  ζ_pow n m hn hm := by rw [← map_pow, I.ζ_pow n m hn hm]
  ev n a := qkExt hB f hf (I.ev n a)
  add n hn a b := qkAdd_of_qkExt hB f hf ((qkExt_iff hB f hf _ _).2 rfl) ((qkExt_iff hB f hf _ _).2 rfl)
    ((qkExt_iff hB f hf _ _).2 rfl) (I.add n hn a b)
  lin n hn x a := letI := H.starRing
    qkAct_of_qkExt hB f hf hL.globalFns oa ((qkExt_iff hB f hf _ _).2 rfl) ((qkExt_iff hB f hf _ _).2 rfl)
      (I.lin n hn x a)
  ker n hn a b := (equiv_qkExt_iff f hf hB _ _).trans (I.ker n hn a b)
  onto n hn p' := by
    obtain ⟨p, rfl⟩ := exists_qkExt f hf hB hL (Nat.cast_ne_zero.2 hn.ne') p'
    exact (I.onto n hn p).imp fun a h => qkExt_congr hB f hf h
  tower n m hn hm a := by
    obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm a
    refine ⟨qkExt hB f hf q, h₁, (isNsmul_iff_eq _ _ _).2 ?_, qkExt_congr hB f hf h₃⟩
    show gtExt D f hf q.g = m • gtExt D f hf _
    rw [(isNsmul_iff_eq _ _ _).1 h₂, map_nsmul]
  isom n hn a b := by
    have := hw n hn _ _ _ (I.isom n hn a b)
    rw [← map_zpow]
    exact this

end GlobalTheory.ArcExt
end
