import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardExactGramIntegralFrameClassesLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsExactGramFrameInTermClassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLatticeStatement

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrCount

open GlobalTheory.LoopC.FrEqv

theorem cntCl_le_of_map {α β : Type} {R : α → α → Prop} {R' : β → β → Prop} (hR : Equivalence R)
    (hR' : Equivalence R') (X : Set α) (Y : Set β) (φ : α → β)
    (h1 : ∀ a ∈ X, ∃ c, R a c ∧ φ c ∈ Y) (h2 : ∀ c c', R' (φ c) (φ c') → R c c') :
    cntCl X R ≤ cntCl Y R' := by
  rw [cntCl_eq_encard hR, cntCl_eq_encard hR']
  refine le_trans (Set.encard_le_encard ?_)
    (Set.encard_image_le (fun C : Set β => {d | ∃ c, φ c ∈ C ∧ R c d}) _)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc, hY⟩ := h1 a ha
  refine ⟨_, ⟨φ c, hY, rfl⟩, ?_⟩
  ext d
  constructor
  · rintro ⟨c', h3, h4⟩
    exact hR.trans hc (hR.trans (h2 c c' h3) h4)
  · intro hd
    exact ⟨c, hR'.refl _, hR.trans (hR.symm hc) hd⟩

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def mapFlag (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (G : LFlag S r T') : LFlag S r T' where
  fl :=
    { e := fun a => n (G.fl.e a)
      z := n G.fl.z
      e_indep := G.fl.e_indep.map' (n : S.V →ₗ[E] S.V) (LinearEquiv.ker n)
      e_iso := fun a b => (hn _ _).trans (G.fl.e_iso a b)
      z_orth := fun a => (hn _ _).trans (G.fl.z_orth a)
      z_norm := (hn _ _).trans G.fl.z_norm }
  zt := n G.zt

theorem frame_mapFlag (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (G : LFlag S r T') (b : Fin (r + 1)) :
    frame (mapFlag n hn G) b = n (frame G b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b
  · simp [frame, FlagG.fvec, mapFlag]
  · simp [frame, FlagG.fvec, mapFlag]

theorem symm_mem_X_mapFlag (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (G : LFlag S r T') {y : S.V}
    (hy : y ∈ Xsp (mapFlag n hn G)) : n.symm y ∈ Xsp G := by
  have : Xsp (mapFlag n hn G) ≤ (Xsp G).comap (n.symm : S.V →ₗ[E] S.V) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    change n.symm (n (G.fl.e a)) ∈ Xsp G
    rw [n.symm_apply_apply]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact this hy

theorem fix_X {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hf : ∀ b, n (frame F b) = frame F b) {x : S.V}
    (hx : x ∈ Xsp F) : n x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := hf a.castSucc
    simpa [frame, FlagG.fvec] using this
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem isometry_fix_flagAnisotropicVector_of_fix_frame {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hf : ∀ b, n (frame F b) = frame F b) :
    n F.fl.z = F.fl.z := by
  have := hf (Fin.last _)
  simpa [frame, FlagG.fvec] using this

theorem symm_fix {n : S.V ≃ₗ[E] S.V} {x : S.V} (h : n x = x) : n.symm x = x := by
  conv_lhs => rw [← h]
  simp

theorem Xflag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem mem_orth' {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem ap_mem_gmap {Λ : Submodule (𝓞 E) S.V} (n : S.V ≃ₗ[E] S.V) (x : S.V) :
    n x ∈ Formalism.HermitianLatticesTheory.gmap n Λ ↔ x ∈ Λ := by
  rw [mem_gmap, n.symm_apply_apply]

theorem Lsub_gmap {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (Λ : Submodule (𝓞 E) S.V)
    (ho : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) : Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  unfold Lsub
  congr 1
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨h1, h2⟩
    have h3 : n.symm y - y ∈ Xsp F := symm_sub_mem n X_le_orth ho y h2
    have h4 : n.symm y ∈ orth S (Xsp F) := by
      simpa using (orth S (Xsp F)).add_mem (X_le_orth h3) h2
    have e : y = n.symm y - (n.symm y - y) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨(mem_gmap n y).1 h1, h4⟩) (Submodule.mem_sup_right h3)
  · refine sup_le ?_ le_sup_right
    rintro y ⟨h1, h2⟩
    have h3 : n y - y ∈ Xsp F := ho y h2
    have h4 : n y ∈ orth S (Xsp F) := by
      simpa using (orth S (Xsp F)).add_mem (X_le_orth h3) h2
    have e : y = n y - (n y - y) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨(ap_mem_gmap n y).2 h1, h4⟩) (Submodule.mem_sup_right h3)

theorem conj_mem_NLam {F : LFlag S r T} {n m : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b)
    (ho : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) (hm : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap n Λ) F) :
    n.symm * (m * n) ∈ NLam Λ F := by
  refine ⟨⟨mul_mem (inv_mem hn) (mul_mem hm.1.1 hn), ?_⟩, fun j x hx => ?_, ?_⟩
  · ext x
    rw [mem_gmap, ← ap_mem_gmap n, ← aut_mem_iff hm.1, mem_gmap]
    change (n.symm * (m * n)) ((n.symm * (m * n)).symm x) ∈ Λ ↔ _
    simp
  · have h1 : n x = x := fix_X hf (Xflag_le_X F _ hx)
    have h2 := hm.2.1 j x hx
    have h3 : m x ∈ Xsp F := by
      simpa using (Xsp F).add_mem (Xflag_le_X F _ h2) (Xflag_le_X F _ hx)
    change n.symm (m (n x)) - x ∈ _
    rw [h1, symm_fix (fix_X hf h3)]
    exact h2
  · exact trans_sub_mem _ _ X_le_orth (trans_sub_mem _ _ X_le_orth ho hm.2.2) (symm_sub_mem n X_le_orth ho)

theorem X_le_UUE {F : LFlag S r T} (G : LFlag S r T') {Λ : Submodule (𝓞 E) S.V}
    (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) : Xsp F ≤ UUE Λ F G := by
  intro x hx
  have h0 : x ∈ Submodule.span E (Λ : Set S.V) := hΛ ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ x h0
  rw [Submodule.span_eq] at ht
  have h1 : (t : 𝓞 E) • x ∈ UU Λ F G :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      ⟨ht, (toO S (Xsp F)).smul_mem (t : 𝓞 E) hx⟩))
  have h2 : ((t : 𝓞 E) : E) • x ∈ UUE Λ F G := by
    have : ((t : 𝓞 E) : E) • x = (t : 𝓞 E) • x := algebraMap_smul E (t : 𝓞 E) x
    rw [this]
    exact Submodule.subset_span h1
  have h3 : ((t : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero t.2
    exact_mod_cast this
  exact (Submodule.smul_mem_iff _ h3).1 h2

theorem Thp_map {F : LFlag S r T} (G : LFlag S r T') {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b) (hz : F.zt = F.fl.z) {t : S.V}
    (ht : t ∈ Thp Λ F G) : n t ∈ Thp (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) := by
  refine ⟨(ap_mem_gmap n t).2 ht.1, ?_⟩
  have key : UUE (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) ≤ (UUE Λ F G).comap (n.symm : S.V →ₗ[E] S.V) := by
    refine Submodule.span_le.mpr ?_
    have : UU (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) ≤ Formalism.HermitianLatticesTheory.gmap n (UU Λ F G) := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · rintro y ⟨h1, h2⟩
        rw [mem_gmap]
        refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
          ⟨(mem_gmap n y).1 h1, ?_⟩))
        rw [symm_fix (fix_X hf h2)]
        exact h2
      · refine Submodule.span_le.mpr ?_
        rintro _ rfl
        change F.zt ∈ Formalism.HermitianLatticesTheory.gmap n (UU Λ F G)
        rw [mem_gmap, symm_fix (show n F.zt = F.zt by rw [hz]; exact isometry_fix_flagAnisotropicVector_of_fix_frame hf)]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.mem_span_singleton_self _)))
      · rintro y ⟨h1, h2⟩
        rw [mem_gmap]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right
          ⟨(mem_gmap n y).1 h1, symm_mem_X_mapFlag n hn G h2⟩)
      · refine Submodule.span_le.mpr ?_
        rintro _ rfl
        change n G.zt ∈ Formalism.HermitianLatticesTheory.gmap n (UU Λ F G)
        rw [ap_mem_gmap]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    intro y hy
    exact Submodule.subset_span ((mem_gmap n y).1 (this hy))
  change n t ∈ orth S _
  rw [mem_orth']
  intro x hx
  have h1 := (mem_orth'.1 ht.2) _ (key hx)
  have h2 := hn (n.symm x) t
  rw [n.apply_symm_apply] at h2
  exact h2.trans h1

theorem Thp_sup_le {F : LFlag S r T} (G : LFlag S r T') {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b)
    (ho : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) (hz : F.zt = F.fl.z) :
    Thp Λ F G ⊔ toO S (Xsp F) ≤ Thp (Formalism.HermitianLatticesTheory.gmap n Λ) F (mapFlag n hn G) ⊔ toO S (Xsp F) := by
  refine sup_le ?_ le_sup_right
  intro t ht
  have h1 : t ∈ orth S (Xsp F) := mem_orth'.2 fun x hx => mem_orth'.1 ht.2 x (X_le_UUE G hΛ hx)
  have e : t = n t - (n t - t) := by abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Thp_map G hn hf hz ht)) (Submodule.mem_sup_right (ho t h1))

theorem Zhat_mapFlag {F : LFlag S r T} (G : LFlag S r T') {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hf : ∀ b, n (frame F b) = frame F b) :
    ZhatL F (mapFlag n hn G) = ZhatL F G := by
  funext a b
  change S.hT (frame F a) (frame (mapFlag n hn G) b) = S.hT (frame F a) (frame G b)
  rw [frame_mapFlag, ← hn (frame F a) (frame G b), hf]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntFr D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  intro D u u' F0 Λ hS hB hR P Z s De Q hs hk hP hQ
  obtain ⟨n, ⟨hn, hf, ho⟩, hsp, hR'⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ hB hR hS.2.1.one_lt.le
  have hL : L0X D (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = L0X D Λ (lf D F0) := by
    unfold L0X L0sub
    rw [Lsub_gmap Λ ho]
  refine le_trans ?_ (GlobalTheory.T.card_exactGramIntegralFrameClasses_le D u u' F0 _ hS hB hR' hsp P Z s De Q hs hk (hL ▸ hP) hQ)
  refine ENat.toENNReal_le.2 ?_
  refine cntCl_le_of_map (TEqv_equivalence D Λ _) (TEqv_equivalence D _ _) _ _ (mapFlag n hn) ?_ ?_
  · intro a ha
    obtain ⟨c, ⟨c1, c2, c3, c4⟩, hc⟩ := GlobalTheory.T.exists_exactGram_frame_in_termClass D u u' F0 Λ hS hB hR P Z a ha
    refine ⟨c, hc, ⟨(ap_mem_gmap n _).2 c1.1, congrArg n c1.2⟩, fun a => (ap_mem_gmap n _).2 (c2 a),
      (Zhat_mapFlag c hn hf).trans c3, c4.trans ?_⟩
    exact Submodule.comap_mono (Thp_sup_le c hR.2.1.1.span_eq_top hn hf ho rfl)
  · rintro c c' ⟨m, hm, ξ, h1, h2, h3⟩
    refine ⟨_, conj_mem_NLam hn hf ho hm, ξ, h1, h2, ?_⟩
    have h4 := map_frameAct n.symm (fun a => m (frame (mapFlag n hn c) a)) ξ
    rw [← h3] at h4
    simp only [frame_mapFlag, LinearEquiv.symm_apply_apply] at h4
    exact h4

end GlobalTheory.LoopC.FrCount

end
