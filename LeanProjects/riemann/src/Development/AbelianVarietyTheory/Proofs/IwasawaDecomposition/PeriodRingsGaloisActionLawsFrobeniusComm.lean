import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.MemLoc.ActLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem mem_map_of_evalₐ_eq_zero_pt (I : Ideal R) (hI : I.FG) (n : ℕ) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I n z = 0) : z ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  have h5 : z ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    induction z using AdicCompletion.induction_on with
    | _ z =>
      rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
      change Submodule.Quotient.mk (z.1 n) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa using hz
  rw [Ideal.smul_top_eq_map] at h5
  exact h5

theorem evalₐ_alg_pt (I : Ideal R) (n : ℕ) (y : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) y) = Ideal.Quotient.mk (I ^ n) y :=
  (AdicCompletion.evalₐ I n).commutes y

theorem evalₐ_hom_pt (I : Ideal R) (hI : I.FG) (K : Ideal S) (f : R →+* S) (hf : I ≤ K.comap f)
    (φ : AdicCompletion I R →+* AdicCompletion K S)
    (hφ : ∀ r, φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (n : ℕ) (x : AdicCompletion I R) (y : R) (hy : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) y) :
    AdicCompletion.evalₐ K n (φ x) = Ideal.Quotient.mk (K ^ n) (f y) := by
  have h1 : x - algebraMap R (AdicCompletion I R) y ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) :=
    mem_map_of_evalₐ_eq_zero_pt I hI n _ (by rw [map_sub, hy, evalₐ_alg_pt, sub_self])
  have h2 : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤
      RingHom.ker ((AdicCompletion.evalₐ K n).toRingHom.comp φ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h3 : f r ∈ K ^ n := Ideal.le_comap_pow f n (Ideal.pow_right_mono hf n hr)
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hφ]
    exact (evalₐ_alg_pt K n (f r)).trans (Ideal.Quotient.eq_zero_iff_mem.2 h3)
  have h4 : AdicCompletion.evalₐ K n (φ (x - algebraMap R (AdicCompletion I R) y)) = 0 := h2 h1
  rw [map_sub, map_sub, hφ, evalₐ_alg_pt, sub_eq_zero] at h4
  exact h4

theorem hom_ext_pt (I : Ideal R) (hI : I.FG) (K : Ideal S) (f : R →+* S) (hf : I ≤ K.comap f)
    (φ ψ : AdicCompletion I R →+* AdicCompletion K S)
    (hφ : ∀ r, φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (hψ : ∀ r, ψ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (x : AdicCompletion I R) : φ x = ψ x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [evalₐ_hom_pt I hI K f hf φ hφ n x y hy.symm, evalₐ_hom_pt I hI K f hf ψ hψ n x y hy.symm]

theorem endo_ext_pt {A : Type} [CommRing A] (I : Ideal R) (hI : I.FG) (i : R →+* A) (e : A ≃+* AdicCompletion I R)
    (he : ∀ r, e (i r) = algebraMap R (AdicCompletion I R) r) (f : R →+* R) (hf : I ≤ I.comap f)
    (φ ψ : A →+* A) (hφ : ∀ r, φ (i r) = i (f r)) (hψ : ∀ r, ψ (i r) = i (f r)) (x : A) : φ x = ψ x := by
  have hs : ∀ r, e.symm (algebraMap R (AdicCompletion I R) r) = i r := fun r => by
    rw [← he, RingEquiv.symm_apply_apply]
  have h := hom_ext_pt I hI I f hf (e.toRingHom.comp (φ.comp e.symm.toRingHom))
    (e.toRingHom.comp (ψ.comp e.symm.toRingHom))
    (fun r => by
      change e (φ (e.symm _)) = _
      rw [hs, hφ, he])
    (fun r => by
      change e (ψ (e.symm _)) = _
      rw [hs, hψ, he]) (e x)
  change e (φ (e.symm (e x))) = e (ψ (e.symm (e x))) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact e.injective h

theorem span_le_comap_pt (p : ℕ) (f : R →+* S) : Ideal.span {(p : R)} ≤ (Ideal.span {(p : S)}).comap f := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

theorem compMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal T) (f : R →+* S) (g : S →+* T) (k : R →+* T)
    (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) (hk : I ≤ K.comap k) (e : ∀ x, k x = g (f x))
    (x : AdicCompletion I R) :
    GlobalTheory.AdicMaps.adicMap I K k hk x = GlobalTheory.AdicMaps.adicMap J K g hg (GlobalTheory.AdicMaps.adicMap I J f hf x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [GlobalTheory.AdicMaps.evalₐ_adicMap_mk I K k hk n x y hy.symm,
    GlobalTheory.AdicMaps.evalₐ_adicMap_mk J K g hg n _ (f y) (GlobalTheory.AdicMaps.evalₐ_adicMap_mk I J f hf n x y hy.symm), e]

theorem compMap_id (I : Ideal R) (f : R →+* R) (hf : I ≤ I.comap f) (e : ∀ x, f x = x)
    (x : AdicCompletion I R) : GlobalTheory.AdicMaps.adicMap I I f hf x = x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [GlobalTheory.AdicMaps.evalₐ_adicMap_mk I I f hf n x y hy.symm, e, hy]

end

variable {l : ℕ} [Fact l.Prime]

theorem awayMap_comp₂ (f g k : Per.Ainf l →+* Per.Ainf l) (e : ∀ x, k x = g (f x)) (x : Per.AinfP l) :
    Per.extP k x = Per.extP g (Per.extP f x) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := Per.extP k) (k := (Per.extP g).comp (Per.extP f)) (RingHom.ext fun y => ?_)) x
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, e]

theorem awayMap_id₂ (f : Per.Ainf l →+* Per.Ainf l) (e : ∀ x, f x = x) (x : Per.AinfP l) :
    Per.extP f x = x := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := Per.extP f) (k := RingHom.id _) (RingHom.ext fun y => ?_)) x
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, e, RingHom.id_apply]

theorem acris_ext_pt (f : Per.Acris0 l →+* Per.Acris0 l) (φ ψ : Per.Acris l →+* Per.Acris l)
    (hφ : ∀ r, φ (algebraMap (Per.Acris0 l) (Per.Acris l) r) = algebraMap (Per.Acris0 l) (Per.Acris l) (f r))
    (hψ : ∀ r, ψ (algebraMap (Per.Acris0 l) (Per.Acris l) r) = algebraMap (Per.Acris0 l) (Per.Acris l) (f r))
    (x : Per.Acris l) : φ x = ψ x := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  exact endo_ext_pt _ (Submodule.fg_span_singleton _) (algebraMap (Per.Acris0 l) (Per.Acris l)) e he f
    (span_le_comap_pt l f) φ ψ hφ hψ x

theorem bdRp_ext_pt (f : Per.AinfP l →+* Per.AinfP l) (hf : Per.kerP l ≤ (Per.kerP l).comap f)
    (φ ψ : Per.BdRp l →+* Per.BdRp l)
    (hφ : ∀ r, φ (algebraMap (Per.AinfP l) (Per.BdRp l) r) = algebraMap (Per.AinfP l) (Per.BdRp l) (f r))
    (hψ : ∀ r, ψ (algebraMap (Per.AinfP l) (Per.BdRp l) r) = algebraMap (Per.AinfP l) (Per.BdRp l) (f r))
    (x : Per.BdRp l) : φ x = ψ x := by
  obtain ⟨e, he, -⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have hfg : (Per.kerP l).FG := by
    obtain ⟨ε, hε⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
    rw [(GlobalTheory.MemLoc.thetaP_facts l).2.2.2.2.2.2 ε hε]
    exact Submodule.fg_span_singleton _
  exact endo_ext_pt _ hfg (algebraMap (Per.AinfP l) (Per.BdRp l)) e he f hf φ ψ hφ hψ x

theorem extends_comp {f g k : Per.Ainf l →+* Per.Ainf l} {F G K : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) (hg : GlobalTheory.CrisMaps.Extends g G) (hk : GlobalTheory.CrisMaps.Extends k K)
    (e : ∀ x, k x = g (f x)) (x : Per.Acris l) : K x = G (F x) :=
  acris_ext_pt ((Per.extP k).restrict _ _ hk.mem) K (G.comp F)
    (fun r => hk.env r)
    (fun r => by
      rw [RingHom.comp_apply, hf.env, hg.env]
      exact congrArg _ (Subtype.ext (awayMap_comp₂ f g k e r).symm)) x

theorem extends_id {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) (e : ∀ x, f x = x) (x : Per.Acris l) : F x = x :=
  acris_ext_pt (RingHom.id _) F (RingHom.id _)
    (fun r => (hf.env r).trans (congrArg _ (Subtype.ext (awayMap_id₂ f e r))))
    (fun _ => rfl) x

theorem sigA_mul (g h : Per.Gq l) (x : Per.Acris l) : sigA (g * h) x = sigA g (sigA h x) :=
  extends_comp (GlobalTheory.CrisMaps.sigA_extends h) (GlobalTheory.CrisMaps.sigA_extends g) (GlobalTheory.CrisMaps.sigA_extends (g * h))
    (GlobalTheory.RingBasics.σA_mul g h) x

theorem sigA_one (x : Per.Acris l) : sigA 1 x = x :=
  extends_id (GlobalTheory.CrisMaps.sigA_extends 1) GlobalTheory.RingBasics.σA_one x

theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

theorem σDp_mul (g h : Per.Gq l) (x : Per.BdRp l) : Per.σDp (g * h) x = Per.σDp g (Per.σDp h x) :=
  bdRp_ext_pt (Per.extP (Per.σA (g * h))) (GlobalTheory.RingBasics.ker_σ (g * h)) (Per.σDp (g * h)) ((Per.σDp g).comp (Per.σDp h))
    (GlobalTheory.RingIface.sigDp_alg l (g * h))
    (fun r => by
      rw [RingHom.comp_apply, GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingIface.sigDp_alg,
        awayMap_comp₂ _ _ _ (GlobalTheory.RingBasics.σA_mul g h)]) x

theorem σDp_one (x : Per.BdRp l) : Per.σDp 1 x = x :=
  bdRp_ext_pt (Per.extP (Per.σA (1 : Per.Gq l))) (GlobalTheory.RingBasics.ker_σ 1) (Per.σDp 1) (RingHom.id _)
    (GlobalTheory.RingIface.sigDp_alg l 1)
    (fun r => by rw [RingHom.id_apply, awayMap_id₂ _ GlobalTheory.RingBasics.σA_one]) x

theorem σDp_alg (g : Per.Gq l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem σD_mul (g h : Per.Gq l) (x : Per.BdR l) : Per.σD (g * h) x = Per.σD g (Per.σD h x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bdR_hom_ext l
    (f := Per.σD (g * h)) (g := (Per.σD g).comp (Per.σD h)) fun y => ?_) x
  simp only [RingHom.comp_apply, σD_alg, σDp_mul]

theorem σD_one (x : Per.BdR l) : Per.σD 1 x = x := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bdR_hom_ext l
    (f := Per.σD 1) (g := RingHom.id _) fun y => ?_) x
  simp only [RingHom.comp_apply, σD_alg, σDp_one, RingHom.id_apply]

theorem endo_zA_pt (F : Per.Ainf l →+* Per.Ainf l) (z : ℤ_[l]) : F (Per.zA l z) = Per.zA l z := by
  rw [← sub_eq_zero]
  refine WittVector.ext fun m => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (m + 1) z)
  have hz : z = (z.appr (m + 1) : ℤ_[l]) + w * (l : ℤ_[l]) ^ (m + 1) := by rw [hw]; ring
  have h : F (Per.zA l z) - Per.zA l z ∈ Ideal.span {((l : ℕ) : Per.Ainf l) ^ (m + 1)} := by
    refine Ideal.mem_span_singleton'.2 ⟨F (Per.zA l w) - Per.zA l w, ?_⟩
    generalize z.appr (m + 1) = a at hz
    rw [hz]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [(WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 h m (Nat.lt_succ_self m), WittVector.zero_coeff]

theorem map_zA (f : Per.Fl l →+* Per.Fl l) (z : ℤ_[l]) :
    WittVector.map f (Per.zA l z) = Per.zA l z :=
  endo_zA_pt (WittVector.map f) z

theorem φA_σA (g : Per.Gq l) (a : Per.Ainf l) : Per.φA l (Per.σA g a) = Per.σA g (Per.φA l a) := by
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.phiA_coeff, GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff,
    map_pow]

theorem φB_σB (g : Per.Gq l) (x : Per.Bcris l) : Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := (Per.φB l).comp (Per.σB g)) (g := (Per.σB g).comp (Per.φB l)) fun y => ?_) x
  simp only [RingHom.comp_apply, GlobalTheory.CrisMaps.φB_phiA, GlobalTheory.CrisMaps.σB_sigA, GlobalTheory.CrisMaps.phiA_sigA]

theorem σB_mul (g h : Per.Gq l) (x : Per.Bcris l) : Per.σB (g * h) x = Per.σB g (Per.σB h x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := Per.σB (g * h)) (g := (Per.σB g).comp (Per.σB h)) fun y => ?_) x
  simp only [RingHom.comp_apply, GlobalTheory.CrisMaps.σB_sigA, sigA_mul]

theorem σB_one (x : Per.Bcris l) : Per.σB 1 x = x := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := Per.σB 1) (g := RingHom.id _) fun y => ?_) x
  simp only [GlobalTheory.CrisMaps.σB_sigA, sigA_one, RingHom.id_apply]

theorem σB_aB (g : Per.Gq l) (a : Per.Ainf l) : Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.CrisMaps.σB_sigA, (GlobalTheory.CrisMaps.sigA_extends g).alg]

theorem φB_aB (a : Per.Ainf l) : Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.CrisMaps.φB_phiA, (GlobalTheory.CrisMaps.phiA_extends l).alg]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (g h : Per.Gq l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)) ∧
    (∀ x : Per.Bcris l, Per.σB 1 x = x) ∧
    (∀ (g h : Per.Gq l) (x : Per.BdR l), Per.σD (g * h) x = Per.σD g (Per.σD h x)) ∧
    (∀ x : Per.BdR l, Per.σD 1 x = x) ∧
    (∀ (g : Per.Gq l) (x : Per.Bcris l), Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x)) ∧
    (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a)) ∧
    (∀ a : Per.Ainf l, Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a)) ∧
    (∀ (g : Per.Gq l) (z : ℤ_[l]), Per.σA g (Per.zA l z) = Per.zA l z) ∧
    (∀ z : ℤ_[l], Per.φA l (Per.zA l z) = Per.zA l z) ∧
    (∀ (g : Per.Gq l) (y : Per.BdRp l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y)) ∧
    (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σDp g (aDp l a) = aDp l (Per.σA g a)) ∧
    (∀ (g : Per.Gq l) (x : Per.Acris l), Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x)) ∧
    ∀ x : Per.Acris l, Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  fun l _ => ⟨σB_mul, σB_one, σD_mul, σD_one, φB_σB, σB_aB, φB_aB,
    fun g => endo_zA_pt (Per.σA g), endo_zA_pt (Per.φA l),
    σD_alg, σDp_aDp, GlobalTheory.CrisMaps.σB_sigA, GlobalTheory.CrisMaps.φB_phiA l⟩

end GlobalTheory.MemLoc.ActLaws
