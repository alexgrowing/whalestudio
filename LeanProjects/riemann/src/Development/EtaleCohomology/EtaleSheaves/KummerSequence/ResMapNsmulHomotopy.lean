import Development.EtaleCohomology.EtaleSheaves.LeafKumDeltaPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuMapPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPfGlue
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.GmSepPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPowPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPrimPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafUnitRootPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder

open LateralTheory.E.E4 LeafKumSeqPf KummerH0Surjection

theorem resMap_nsmul_homotopy (F : Shv ℤ) (q : ℕ) :
    Nonempty (Homotopy (resMap ℤ (q • 𝟙 F)) (q • 𝟙 (res ℤ F))) := by
  refine ⟨?_⟩
  have H : Homotopy (InjectiveResolution.desc (q • 𝟙 F) (injectiveResolution F) (injectiveResolution F))
      (q • 𝟙 (injectiveResolution F).cocomplex) :=
    InjectiveResolution.descHomotopy (q • 𝟙 F) _ _ (by simp)
      (by simp [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Functor.map_nsmul])
  refine (H.extend ComplexShape.embeddingUpNat).trans (Homotopy.ofEq ?_)
  exact ((ComplexShape.embeddingUpNat.extendFunctor (Shv ℤ)).map_nsmul).trans
    (congrArg (q • ·) ((ComplexShape.embeddingUpNat.extendFunctor (Shv ℤ)).map_id _))

theorem ofHom_nsmul {K L : Cx ℤ} (f : K ⟶ L) (q : ℕ) : Cochain.ofHom (q • f) = q • Cochain.ofHom f := by
  induction q with
  | zero => simp
  | succ q ih => rw [succ_nsmul, succ_nsmul, Cochain.ofHom_add, ih]

theorem comp_nsmul' {K L M : Cx ℤ} {n : ℤ} (a : Cochain K L n) (b : Cochain L M 0) (q : ℕ) :
    a.comp (q • b) (add_zero n) = q • a.comp b (add_zero n) := by
  induction q with
  | zero => simp
  | succ q ih => rw [succ_nsmul, succ_nsmul, Cochain.comp_add, ih]

theorem mk_nsmul {K L : Cx ℤ} {n : ℤ} (a : Cocycle K L n) (q : ℕ) :
    CohomologyClass.mk (q • a) = q • CohomologyClass.mk a := by
  induction q with
  | zero => simp
  | succ q ih => rw [succ_nsmul, succ_nsmul, CohomologyClass.mk_add, ih]

theorem post_nsmul (K : Cx ℤ) (F : Shv ℤ) (q : ℕ) (n : ℤ) (x : HK ℤ K F n) :
    HK.post ℤ K (q • 𝟙 F) n x = q • x := by
  obtain ⟨H⟩ := resMap_nsmul_homotopy F q
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  rw [← mk_nsmul]
  show CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy H) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero, ofHom_nsmul,
    Cochain.comp_sub, comp_nsmul']
  simp [zcomp]
  rfl

theorem powGm_eq (q : ℕ) : powGm q = q • 𝟙 Gm := by
  have h : Functor.whiskerLeft Scheme.Γ (powNat q) = q • 𝟙 (Scheme.Γ ⋙ unitsF) := by
    ext U x
    simp [powNat]
    rfl
  unfold powGm
  rw [h, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

theorem muUnits : LeafKumMuPf.LeafKumMuUnits := by
  have hI := LeafKumMuInjPfGlue.LeafKumMuInj_of TwLocGenPf.TwLocGen_of GmSepPf.GmSep_of
  exact LeafKumMuUnitsPf.LeafKumMuUnits_of LeafKumMuMapPf.LeafKumMuMap_of hI
    (LeafKumMuSurjPf.etale_mu_twist_sections_surj_of_prim_root_pow_inj LeafKumMuSurjPrimPf.LeafKumMuSurjPrim_of
      LeafKumMuSurjPowPf.LeafKumMuSurjPow_of hI)

theorem kumSecSurj : LeafKumSecSurj := LeafKumSecSurjPf.LeafKumSecSurj_of LeafUnitRootPf.LeafUnitRoot_of

theorem unit_of_over (q : ℕ) {Ω : Type} [CommRing Ω] (hq : IsUnit (q : Ω)) {U : Scheme.{0}} (x : U ⟶ Sp Ω) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ x.appTop).hom

theorem kumSeq : LateralTheory.E.LeafKumDeltaPf.LeafKumSeq := by
  intro hy q _ Ω _ _ hq C c hc
  have hA7 : A7 := hy.2.2.2.2.2.1
  have hA8 : A8 := hy.2.2.2.2.2.2.1
  have hA10 : A10 := hy.2.2.2.2.2.2.2.2.1
  obtain ⟨a, ha0⟩ := LeafKumMuPf.LeafKumMuSec_of muUnits q Ω hq
  have ha := hA10 ℤ (sch.obj C) a (fun U ⟨x⟩ => ha0 U ⟨(show U ⟶ C from x) ≫ c⟩) 2
  have hβ := hA10 ℤ (sch.obj C) (kumM q) (fun U ⟨x⟩ =>
    ⟨sec_injective _ U, kumSecSurj q U (unit_of_over q hq ((show U ⟶ C from x) ≫ c))⟩) 1
  set K := (chains ℤ).obj (sch.obj C) with hK
  obtain ⟨z, hz⟩ := hA7 ℤ (kumSC q) (kumSC_shortExact q)
  obtain ⟨_, hex1, hex2⟩ := hz K 1
  have hR := hA8 ℤ (ZMod q) (Int.castRingHom (ZMod q)) (sch.obj C) (tw q 1) 2
  let P := AddEquiv.ofBijective (HK.post ℤ K (kumM q) 1) hβ
  let A := AddEquiv.ofBijective (HK.post ℤ K a 2) ha
  let Rr := AddEquiv.ofBijective (restrH (Int.castRingHom (ZMod q)) (sch.obj C) (tw q 1) 2) hR
  let T : Ht q (sch.obj C) 2 1 ≃+ HK ℤ K (kumSC q).X₁ (1 + 1) := Rr.trans A
  let ex : HK ℤ K (kumSC q).X₃ 1 →+ HK ℤ K (kumSC q).X₁ (1 + 1) := HK.ext ℤ K z 1 (1 + 1) rfl
  let fm : HK ℤ K (kumSC q).X₁ (1 + 1) →+ HK ℤ K Gm 2 := HK.post ℤ K (kumSC q).f (1 + 1)
  let gm : HK ℤ K Gm 1 →+ HK ℤ K (kumSC q).X₃ 1 := HK.post ℤ K (kumSC q).g 1
  have e1 : Function.Exact gm ex := hex1
  have e2 : Function.Exact ex fm := hex2
  have hpg : ∀ w, P (gm w) = q • w := by
    intro w
    refine (post_comp ℤ K (kumSC q).g (kumM q) 1 w).symm.trans ?_
    have : (kumSC q).g ≫ kumM q = q • 𝟙 Gm := (cokernel.π_desc _ _ _).trans (powGm_eq q)
    rw [this]
    exact post_nsmul K Gm q 1 w
  refine ⟨T.symm.toAddMonoidHom.comp (ex.comp P.symm.toAddMonoidHom), fm.comp T.toAddMonoidHom, ?_, ?_⟩
  · intro y
    change T.symm (ex (P.symm y)) = 0 ↔ _
    rw [AddEquiv.map_eq_zero_iff, e1]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [← hpg, hw, AddEquiv.apply_symm_apply]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [← hpg, AddEquiv.symm_apply_apply]⟩
  · intro x
    change fm (T x) = 0 ↔ ∃ y, T.symm (ex (P.symm y)) = x
    rw [e2]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨P w, by rw [AddEquiv.symm_apply_apply, hw, AddEquiv.symm_apply_apply]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨P.symm y, (T.apply_symm_apply _).symm⟩

end LateralTheory.E.H2CurveOrder

end
