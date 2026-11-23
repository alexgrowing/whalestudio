import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupBaseChangeIsConnIsEtPerfectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeSemilinearHomDualGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeOfHomEqCompDualHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeEqRigidifiedExtensionPullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeAbsFrobeniusApplyFStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

variable {p : ℕ} [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))

section Main

theorem exists_unique_isTr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) :
    ∃! l', IsTr B σ hG' hG s l l' := by
  letI : Algebra k k' := σ.toAlgebra
  have hb := (GlobalTheory.T.pDivGroupBaseChange_isConn_isEt_perfect p k k' G.dual).1 (dual_conn hG)
  obtain ⟨l', h1, h2⟩ := GlobalTheory.T.etaleDieudonneTranspose_semilinearHom_dualGroups p B k k' G G' (dual_conn hG) (dual_conn hG') hb s l
  exact ⟨l', ⟨hb, h1⟩, fun l'' ⟨_, h⟩ => h2 l'' h⟩

theorem isTr_tr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) :
    IsTr B σ hG' hG s l (tr B hG' hG s l) :=
  tr_spec B hG' hG s l (exists_unique_isTr B hG' hG s l).exists

theorem tr_eq {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (l' : Mod B G' hG')
    (h : IsTr B σ hG' hG s l l') : tr B hG' hG s l = l' :=
  (exists_unique_isTr B hG' hG s l).unique (isTr_tr B hG' hG s l) h

theorem tr_add {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l m : Mod B G hG) :
    tr B hG' hG s (l + m) = tr B hG' hG s l + tr B hG' hG s m := by
  apply tr_eq
  have h1 := isTr_tr B hG' hG s l
  have h2 := isTr_tr B hG' hG s m
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, a1, b1⟩ := h1
  obtain ⟨_, mb, a2, b2⟩ := h2
  refine ⟨hb, lb + mb, fun x => ?_, fun y => ?_⟩
  · rw [LinearMap.add_apply, a1, a2, LinearMap.add_apply, map_add]
  · rw [LinearMap.add_apply, b1, b2, LinearMap.add_apply]

theorem tr_smul {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (a : WittVector p k) (l : Mod B G hG) :
    tr B hG' hG s (a • l) = WittVector.map σ a • tr B hG' hG s l := by
  apply tr_eq
  have h1 := isTr_tr B hG' hG s l
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, a1, b1⟩ := h1
  refine ⟨hb, WittVector.map σ a • lb, fun x => ?_, fun y => ?_⟩
  · rw [LinearMap.smul_apply, a1, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  · rw [LinearMap.smul_apply, b1, LinearMap.smul_apply]

theorem tr_ofHom {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k}
    (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH) :
    tr B hG hH (SemiHom.ofHom f) l = l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f) :=
  tr_eq B hG hH _ l _ (GlobalTheory.T.etaleDieudonneTranspose_ofHom_eq_comp_dualHom p B k G H hG hH f l)

def etBase : Base p (fun _ _ G => G.IsEt) where
  M G h := ModuleCat.of (WittVector p _) (Mod B G h)
  smap h' h s :=
    { toFun := tr B h' h s
      map_zero' := by simpa using tr_smul B h' h s 0 0
      map_add' := tr_add B h' h s }
  red G h := red B G h
  free G h := by
    haveI := B.free G.dual (dual_conn h)
    haveI := B.finite G.dual (dual_conn h)
    change Module.Free (WittVector p _) (Module.Dual _ (B.M G.dual (dual_conn h)))
    infer_instance
  finite G h := by
    haveI := B.free G.dual (dual_conn h)
    haveI := B.finite G.dual (dual_conn h)
    change Module.Finite (WittVector p _) (Module.Dual _ (B.M G.dual (dual_conn h)))
    infer_instance
  red_surjective G h := by
    have hb := PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p _ (p_eq_zero p _) G h
    exact (rigLie G h).symm.surjective.comp
      ((LinearMap.dualMap_surjective_of_injective hb.2.1).comp (redDual_spec B G h).2.1)
  red_eq_zero G h m := by
    have hb := PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p _ (p_eq_zero p _) G h
    change (rigLie G h).symm _ = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff, ← map_zero G.dual.rigOfOmega.dualMap, LinearMap.comp_apply,
      (LinearMap.dualMap_injective_of_surjective hb.2.2).eq_iff]
    exact (redDual_spec B G h).2.2 m
  smap_smul h' h s a m := tr_smul B h' h s a m
  smap_id G h m := by
    change tr B h h _ m = m
    rw [tr_ofHom]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, dualHom_id]
    exact congrArg m (B.smap_id _ _ y)
  smap_add hG hH f g m := by
    change tr B hG hH _ m = tr B hG hH _ m + tr B hG hH _ m
    rw [tr_ofHom, tr_ofHom, tr_ofHom]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add m,
      map_add (dualHom _ _)]
    exact congrArg m (B.smap_add _ _ _ _ y)
  smap_comp h'' h' h s t u hu m :=
    (tr_eq B h'' h u m _ (GlobalTheory.T.etaleDieudonneTranspose_comp p B _ _ _ _ _ _ _ _ _ h'' h' h s t u hu m _ _
      (isTr_tr B h' h s m) (isTr_tr B h'' h' t _)))
  red_smap h' h s m := GlobalTheory.T.etaleDieudonneTranspose_eq_rigidifiedExtensionPullback p B _ _ _ _ _ h' h s m _ (isTr_tr B h' h s m)

end Main

end GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu

theorem exists_etDual_of_conn : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)),
    ∃ C : Base p (fun _ _ G => G.IsEt), C.EtDual B := by
  intro p _ B
  refine ⟨EtFromConn.etBase B, fun G h hd hG => LinearEquiv.refl _ _, fun G h hd hG => ⟨?_, ?_⟩⟩
  · intro x y
    exact GlobalTheory.T.etaleDieudonneTranspose_absFrobenius_apply_F p B _ G h x _ (EtFromConn.isTr_tr B h h _ x) y
  · intro H h' hd' hH f x y
    exact LinearMap.congr_fun (EtFromConn.tr_ofHom B h h' f x) y

end GlobalTheory.Dieu
