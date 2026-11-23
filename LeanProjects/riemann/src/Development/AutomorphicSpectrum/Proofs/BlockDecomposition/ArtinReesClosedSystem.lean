import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecsMapArrow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobjectStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheavesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GE.Comb

noncomputable section

variable {X : Scheme.{0}} {E : X.Modules}

abbrev QC (S : Subobject E) : Prop := (S : X.Modules).IsQuasicoherent

lemma secs_add {S : Subobject E} {V : X.Opens} {x y : Γ(E, V)} (hx : x ∈ secs S V) (hy : y ∈ secs S V) :
    x + y ∈ secs S V := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add _ _ _⟩

lemma secs_sub {S : Subobject E} {V : X.Opens} {x y : Γ(E, V)} (hx : x ∈ secs S V) (hy : y ∈ secs S V) :
    x - y ∈ secs S V := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ _ _⟩

lemma secs_smul {S : Subobject E} {V : X.Opens} (r : Γ(X, V)) {x : Γ(E, V)} (hx : x ∈ secs S V) :
    r • x ∈ secs S V := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

lemma secs_mono {S T : Subobject E} (h : S ≤ T) (V : X.Opens) : secs S V ⊆ secs T V := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(Subobject.ofLE S T h).app V a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]

lemma secs_inf (S T : Subobject E) (V : X.Opens) : secs (S ⊓ T) V = secs S V ∩ secs T V := by
  have h : S ⊓ T = (Subobject.map S.arrow).obj ((Subobject.pullback S.arrow).obj T) :=
    Subobject.inf_eq_map_pullback S T
  rw [h, GlobalTheory.CompanionTheory.GE.secs_map_arrow, GlobalTheory.CompanionTheory.GE.secs_pullback_arrow]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hy⟩
    exact ⟨x, hy, rfl⟩

lemma modular (hE : E.IsQuasicoherent) {a b c : Subobject E} (ha : QC a) (hb : QC b) (hac : a ≤ c) :
    (a ⊔ b) ⊓ c ≤ a ⊔ (b ⊓ c) := by
  rw [GlobalTheory.CompanionTheory.GE.le_iff_secs_subset]
  intro U x hx
  rw [secs_inf, (GlobalTheory.CompanionTheory.GE.supsecs hE a b ha hb).2 _ U.2] at hx
  obtain ⟨⟨s, hs, t, ht, rfl⟩, hxc⟩ := hx
  have hsc := secs_mono hac _ hs
  have htc : t ∈ secs c U := by
    have := secs_sub hxc hsc
    simpa using this
  exact secs_add (secs_mono le_sup_left _ hs)
    (secs_mono le_sup_right _ ((secs_inf b c U).symm ▸ ⟨ht, htc⟩))

lemma pullback_eq_kernel (D S : Subobject E) :
    (Subobject.pullback D.arrow).obj S = Subobject.mk (kernel.ι (D.arrow ≫ cokernel.π S.arrow)) := by
  have hp := Subobject.isPullback D.arrow S
  apply le_antisymm
  · refine Subobject.le_mk_of_comm (kernel.lift _ ((Subobject.pullback D.arrow).obj S).arrow ?_) ?_
    · rw [← Category.assoc, ← hp.w, Category.assoc, cokernel.condition, comp_zero]
    · simp
  · have hw : (kernel.ι (D.arrow ≫ cokernel.π S.arrow) ≫ D.arrow) ≫ cokernel.π S.arrow = 0 := by
      rw [Category.assoc, kernel.condition]
    let l := Abelian.monoLift S.arrow (kernel.ι (D.arrow ≫ cokernel.π S.arrow) ≫ D.arrow) hw
    refine Subobject.mk_le_of_comm (hp.lift l (kernel.ι _) ?_) (hp.lift_snd _ _ _)
    exact Abelian.monoLift_comp _ _ _

lemma qc_pullback (hE : E.IsQuasicoherent) {D S : Subobject E} (hD : QC D) (hS : QC S) :
    QC ((Subobject.pullback D.arrow).obj S) := by
  haveI : E.IsQuasicoherent := hE
  haveI : (D : X.Modules).IsQuasicoherent := hD
  haveI : (S : X.Modules).IsQuasicoherent := hS
  rw [QC, pullback_eq_kernel]
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι (D.arrow ≫ cokernel.π S.arrow))).symm inferInstance

lemma qc_map {D : Subobject E} {B : Subobject (D : X.Modules)} (hB : QC B) :
    QC ((Subobject.map D.arrow).obj B) := by
  have hm : (Subobject.map D.arrow).obj B = Subobject.mk (B.arrow ≫ D.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    rfl
  rw [QC, hm]
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (B.arrow ≫ D.arrow)).symm hB

lemma qc_inf (hE : E.IsQuasicoherent) {S T : Subobject E} (hS : QC S) (hT : QC T) : QC (S ⊓ T) := by
  rw [Subobject.inf_eq_map_pullback]
  exact qc_map (qc_pullback hE hS hT)

lemma map_sup' (D : Subobject E) (a b : Subobject (D : X.Modules)) :
    (Subobject.map D.arrow).obj (a ⊔ b) =
      (Subobject.map D.arrow).obj a ⊔ (Subobject.map D.arrow).obj b :=
  (Subobject.mapPullbackAdj D.arrow).gc.l_sup

lemma secs_eq_univ_of_supportedIn (hE : E.IsQuasicoherent) {S : Subobject E} (hS : QC S) {T : Set X}
    (h : Scheme.Modules.SupportedIn (cokernel S.arrow) T) {U : X.Opens} (hU : IsAffineOpen U)
    (hd : Disjoint (U : Set X) T) : secs S U = Set.univ := by
  haveI : E.IsQuasicoherent := hE
  haveI : (S : X.Modules).IsQuasicoherent := hS
  refine Set.eq_univ_of_forall fun x => ?_
  exact (mem_range_app_iff S.arrow hU x).2 (h U hd _)

lemma supportedIn_of_secs_eq_univ (hE : E.IsQuasicoherent) {S : Subobject E} (hS : QC S) {T : Set X}
    (h : ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) T → secs S U = Set.univ) :
    Scheme.Modules.SupportedIn (cokernel S.arrow) T := by
  haveI : E.IsQuasicoherent := hE
  haveI : (S : X.Modules).IsQuasicoherent := hS
  intro U hU s
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨(cokernel S.arrow).presheaf, (cokernel S.arrow).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {W : X.affineOpens // (W : X.Opens) ≤ U} => (i.1 : X.Opens)) U
    (fun i => homOfLE i.2) ?_ s 0 ?_
  · intro x hx
    obtain ⟨W, ⟨V, hV, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hWU⟩, hxW⟩
  · intro i
    rw [map_zero]
    have hd : Disjoint ((i.1 : X.Opens) : Set X) T := hU.mono_left i.2
    obtain ⟨y, hy⟩ := surjective_cokernel_π_app S.arrow i.1.2
      ((cokernel S.arrow).presheaf.map (homOfLE i.2).op s)
    have hmem : y ∈ secs S i.1 := by rw [h _ i.1.2 hd]; trivial
    rw [← hy]
    exact (mem_range_app_iff S.arrow i.1.2 y).1 hmem

lemma eq_top_of_sup_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (J : Ideal R)
    (N : Submodule R M) (h1 : N ⊔ J • ⊤ = ⊤) (m : ℕ) (h2 : J ^ m • (⊤ : Submodule R M) ≤ N) :
    N = ⊤ := by
  have key : ∀ j : ℕ, N ⊔ J ^ j • (⊤ : Submodule R M) = ⊤ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      apply le_antisymm le_top
      calc (⊤ : Submodule R M) = N ⊔ J ^ j • (⊤ : Submodule R M) := ih.symm
        _ ≤ N ⊔ J ^ (j + 1) • (⊤ : Submodule R M) := by
          refine sup_le le_sup_left ?_
          have h3 : J ^ j • (⊤ : Submodule R M) = J ^ j • (N ⊔ J • ⊤) := by rw [h1]
          rw [h3, Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
          exact sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right
  exact ((key m).symm.trans (sup_eq_left.2 h2)).symm

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

lemma qc_pow (hE : E.IsQuasicoherent) (n : ℕ) : QC (powSub I E n) :=
  haveI : E.IsQuasicoherent := hE
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (idealPowι I E n)).symm inferInstance

lemma powSub_anti (E : X.Modules) {m n : ℕ} (h : m ≤ n) : powSub I E n ≤ powSub I E m := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (powSub_succ_le I E n).trans ih

lemma map_pow_le (hE : E.IsQuasicoherent) {D : Subobject E} (hD : QC D) (n : ℕ) :
    (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) ≤ powSub I E n := by
  rw [GlobalTheory.CompanionTheory.GE.le_iff_secs_subset]
  intro U
  rw [GlobalTheory.CompanionTheory.GE.secs_map_arrow, GlobalTheory.CompanionTheory.GE.secs_powSub I _ hD n _ U.2, GlobalTheory.CompanionTheory.GE.secs_powSub I _ hE n _ U.2]
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ n) • ⊤ :
      Submodule Γ(X, U) Γ((D : X.Modules), U)) := hy
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr m _
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

variable {I} {S : ℕ → Subobject E}

lemma sys_anti (hS : ClosedSys I E S) : Antitone S :=
  antitone_nat_of_succ_le fun e => le_sup_left.trans_eq (hS.succ e).symm

lemma sys_iter (hS : ClosedSys I E S) (e j : ℕ) : S e ≤ S (e + j) ⊔ powSub I E (e + 1) := by
  induction j with
  | zero => exact le_sup_left
  | succ j ih =>
    refine ih.trans (sup_le ((hS.succ (e + j)).le.trans (sup_le le_sup_left ?_)) le_sup_right)
    exact (powSub_anti I E (by omega)).trans le_sup_right

lemma sys_le (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) {D : Subobject E} (hD : QC D) {c : ℕ}
    (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) (e : ℕ) :
    S (e + c) ≤ (D ⊓ S e) ⊔ powSub I E (e + 1) := by
  have h1 : S (e + c) ≤ (powSub I E (e + 1) ⊔ D) ⊓ S e :=
    le_inf (by rw [sup_comm]; exact hc e) (sys_anti hS (by omega))
  refine h1.trans ((modular hE (qc_pow I hE _) hD (hS.pow_le e)).trans ?_)
  rw [sup_comm]

lemma map_restrict (D : Subobject E) (c e : ℕ) :
    (Subobject.map D.arrow).obj (restrictSys I D S c e) =
      (D ⊓ S (e + c)) ⊔ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) := by
  rw [restrictSys, map_sup', Subobject.inf_eq_map_pullback]

lemma map_inj (D : Subobject E) : Function.Injective (Subobject.map D.arrow).obj :=
  Subobject.map_obj_injective D.arrow

lemma restrict_succ (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) {D : Subobject E} (hD : QC D)
    {c k : ℕ} (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1))
    (ar : ∀ n, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n))
    (e : ℕ) :
    restrictSys I D S k e = restrictSys I D S k (e + 1) ⊔ powSub I (D : X.Modules) (e + 1) := by
  apply map_inj D
  rw [map_sup', map_restrict, map_restrict]
  have hQ : (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1 + 1)) ≤
      (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) :=
    (Subobject.map D.arrow).monotone (powSub_succ_le I _ _)
  have hs : e + 1 + k = e + k + 1 := by omega
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    set W := D ⊓ S (e + k + 1) with hW
    have hWq : QC W := qc_inf hE hD (hS.qcoh _)
    have h1 : S (e + k) ≤ W ⊔ powSub I E (e + k + 1) := by
      refine (sys_iter hS (e + k) (1 + c)).trans (sup_le ?_ le_sup_right)
      rw [← add_assoc]
      refine (sys_le hS hE hD hc (e + k + 1)).trans (sup_le le_sup_left ?_)
      exact (powSub_anti I E (by omega)).trans le_sup_right
    have h2 : D ⊓ S (e + k) ≤ (W ⊔ powSub I E (e + k + 1)) ⊓ D :=
      le_inf (inf_le_right.trans h1) inf_le_left
    refine h2.trans ((modular hE hWq (qc_pow I hE _) inf_le_left).trans (sup_le ?_ ?_))
    · rw [hs]
      exact le_sup_left.trans le_sup_left
    · refine le_trans ?_ le_sup_right
      rw [inf_comm, ← hs]
      exact ar (e + 1)
  · rw [hs]
    refine sup_le (sup_le (le_inf inf_le_left ?_ |>.trans le_sup_left) (hQ.trans le_sup_right)) le_sup_right
    exact inf_le_right.trans (sys_anti hS (by omega))

variable {D : Subobject E}

lemma qc_restrict (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D) (c e : ℕ) :
    QC (restrictSys I D S c e) :=
  (GlobalTheory.CompanionTheory.GE.supsecs hD _ _ (qc_pullback hE hD (hS.qcoh _)) (qc_pow I hD _)).1

lemma closedSys_restrict (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D)
    {c k : ℕ} (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1))
    (ar : ∀ n, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n)) :
    ClosedSys I (D : X.Modules) (restrictSys I D S k) where
  qcoh := qc_restrict hS hE hD k
  pow_le _ := le_sup_right
  succ := restrict_succ hS hE hD hc ar

lemma secs_sys_univ (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U)
    (h0 : secs (S 0) U = Set.univ) (n : ℕ) : secs (S n) U = Set.univ := by
  let J : Ideal Γ(X, U) := Ideal.map (toFunctions (A := A) U) I
  let N : Submodule Γ(X, U) Γ(E, U) :=
    { carrier := secs (S n) U
      add_mem' := fun hx hy => secs_add hx hy
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := fun r _ hx => secs_smul r hx }
  have hp : ∀ m, Ideal.map (toFunctions (A := A) U) (I ^ m) = J ^ m := fun m => Ideal.map_pow _ _ _
  have h1 : N ⊔ J • ⊤ = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ secs (S 0) U := by rw [h0]; trivial
    have hle := sys_iter hS 0 n
    rw [zero_add, zero_add] at hle
    have h2 := secs_mono hle U hx
    rw [(GlobalTheory.CompanionTheory.GE.supsecs hE _ _ (hS.qcoh _) (qc_pow I hE _)).2 U hU, GlobalTheory.CompanionTheory.GE.secs_powSub I E hE _ U hU, hp,
      pow_one] at h2
    obtain ⟨s, hs, t, ht, rfl⟩ := h2
    exact Submodule.add_mem_sup hs ht
  have h2 : J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(E, U)) ≤ N := by
    intro x hx
    have := secs_mono (hS.pow_le n) U
    rw [GlobalTheory.CompanionTheory.GE.secs_powSub I E hE _ U hU, hp] at this
    exact this hx
  have h3 := eq_top_of_sup_smul J N h1 (n + 1) h2
  refine Set.eq_univ_of_forall fun x => ?_
  change x ∈ N
  rw [h3]
  trivial

lemma propSupp_restrict (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D)
    (hP : PropSupp A (S 0)) (c : ℕ) : PropSupp A (restrictSys I D S c 0) := by
  obtain ⟨T, hT, hsupp⟩ := hP
  refine ⟨T, hT, supportedIn_of_secs_eq_univ hD (qc_restrict hS hE hD c 0) fun U hU hd => ?_⟩
  have h := secs_sys_univ hS hE hU (secs_eq_univ_of_supportedIn hE (hS.qcoh 0) hsupp hU hd) (0 + c)
  refine Set.eq_univ_of_forall fun x => secs_mono le_sup_left U ?_
  rw [GlobalTheory.CompanionTheory.GE.secs_pullback_arrow]
  change D.arrow.app U x ∈ secs (S (0 + c)) U
  rw [h]
  trivial

lemma alg_of (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D)
    {c k : ℕ} (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1))
    (hprop : ∀ T₁ T₂ : X.IdealSheafData, IsProper (T₁.subschemeι ≫ (X ↘ Spec (.of A))) →
      IsProper (T₂.subschemeι ≫ (X ↘ Spec (.of A))) →
      IsProper ((T₁ ⊓ T₂).subschemeι ≫ (X ↘ Spec (.of A))))
    (halg : Alg I (D : X.Modules) (restrictSys I D S k)) (hPD : PropSupp A D) : Alg I E S := by
  obtain ⟨B', hB'q, hB'P, hB'⟩ := halg
  refine ⟨(Subobject.map D.arrow).obj B', qc_map hB'q, ?_, fun e => ?_⟩
  · obtain ⟨T₁, h1, s1⟩ := hPD
    obtain ⟨T₂, h2, s2⟩ := hB'P
    refine ⟨T₁ ⊓ T₂, hprop T₁ T₂ h1 h2, supportedIn_of_secs_eq_univ hE (qc_map hB'q) fun U hU hd => ?_⟩
    have d1 : Disjoint (U : Set X) (T₁.support : Set X) :=
      hd.mono_right (Scheme.IdealSheafData.support_antitone inf_le_left)
    have d2 : Disjoint (U : Set X) (T₂.support : Set X) :=
      hd.mono_right (Scheme.IdealSheafData.support_antitone inf_le_right)
    have e1 := secs_eq_univ_of_supportedIn hE hD s1 hU d1
    have e2 := secs_eq_univ_of_supportedIn hD hB'q s2 hU d2
    rw [GlobalTheory.CompanionTheory.GE.secs_map_arrow, e2, Set.image_univ]
    exact e1
  · have hmap : (Subobject.map D.arrow).obj B' ⊔
        (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) =
        (D ⊓ S (e + k)) ⊔ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) := by
      rw [← map_sup', hB' e, map_restrict]
    have hQ := map_pow_le I hE hD (e + 1)
    apply le_antisymm
    · refine sup_le ?_ (hS.pow_le e)
      refine le_sup_left.trans (hmap.le.trans (sup_le ?_ (hQ.trans (hS.pow_le e))))
      exact inf_le_right.trans (sys_anti hS (by omega))
    · refine (sys_iter hS e (k + c)).trans (sup_le ?_ le_sup_right)
      rw [← add_assoc]
      refine (sys_le hS hE hD hc (e + k)).trans (sup_le ?_ ?_)
      · refine (le_sup_left.trans hmap.ge).trans (sup_le le_sup_left (hQ.trans le_sup_right))
      · exact (powSub_anti I E (by omega)).trans le_sup_right

end

theorem restrict_alg : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ c : ℕ, (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) → ∃ c' : ℕ, ClosedSys I (D : X.Modules) (restrictSys I D S c') ∧ PropSupp A (restrictSys I D S c' 0) ∧ (Alg I (D : X.Modules) (restrictSys I D S c') → PropSupp A D → Alg I E S) := by
  intro A _ _ I X _ _ _ _ E hE S hS hP D hD c hc
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  obtain ⟨k, ar⟩ := GlobalTheory.T.artin_rees_subobject I hE D hD
  exact ⟨k, closedSys_restrict hS hE.1 hD hc ar, propSupp_restrict hS hE.1 hD hP k,
    fun halg hPD => alg_of hS hE.1 hD hc (fun T₁ T₂ => GlobalTheory.T.proper_inf_ideal_sheaves _ T₁ T₂) halg hPD⟩

end GlobalTheory.CompanionTheory.GE.Comb
