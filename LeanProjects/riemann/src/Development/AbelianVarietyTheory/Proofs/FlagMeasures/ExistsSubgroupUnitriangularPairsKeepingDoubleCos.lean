import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UnitriangularLatticeStabiliserSubFrameAutomorphi
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KeyGroup

variable {D : D7}

theorem mem_iff_of_gmap {a : GV D} {N N' : LV D} (h : Formalism.HermitianLatticesTheory.gmap a N = N') (x : (VS D).V) :
    a x ∈ N' ↔ x ∈ N := by
  rw [← h, GlobalTheory.Unfold.Model.mem_gmap]; simp

theorem gmap_eq_of_iff {a : GV D} {N N' : LV D} (h : ∀ x, a x ∈ N' ↔ x ∈ N) : Formalism.HermitianLatticesTheory.gmap a N = N' := by
  ext y; rw [GlobalTheory.Unfold.Model.mem_gmap, ← h]; simp

theorem orth_iff {β : GV D} (hi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {U U' : Submodule D.host.E (VS D).V}
    (hU : ∀ x, β x ∈ U' ↔ x ∈ U) (y : (VS D).V) : β y ∈ orth (VS D) U' ↔ y ∈ orth (VS D) U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h x hx; rw [← hi]; exact h _ ((hU x).2 hx)
  · intro h x hx
    have e : x = β (β.symm x) := by simp
    rw [e, hi]; exact h _ ((hU _).1 (by rwa [← e]))

theorem lrep_iff {T1 T2 : D.host.E} {F1 : LFlag (VS D) D.R.rS T1} {G1 : LFlag (VS D) D.R.rS T2} {β : GV D}
    {Λ : LV D} (hi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hΛ : ∀ x, β x ∈ Λ ↔ x ∈ Λ)
    (hX : ∀ x, β x ∈ Xsp G1 ↔ x ∈ Xsp F1) (x : (VS D).V) : β x ∈ Lrep Λ G1 ↔ x ∈ Lrep Λ F1 := by
  show (β x ∈ Λ ∧ β x ∈ orth (VS D) (Xsp G1)) ↔ (x ∈ Λ ∧ x ∈ orth (VS D) (Xsp F1))
  exact and_congr (hΛ x) (orth_iff hi hX x)

theorem xlam_iff {T1 T2 : D.host.E} {F1 : LFlag (VS D) D.R.rS T1} {G1 : LFlag (VS D) D.R.rS T2} {β : GV D}
    {Λ : LV D} (hΛ : ∀ x, β x ∈ Λ ↔ x ∈ Λ)
    (hX : ∀ x, β x ∈ Xsp G1 ↔ x ∈ Xsp F1) (x : (VS D).V) : β x ∈ XLam Λ G1 ↔ x ∈ XLam Λ F1 := by
  show (β x ∈ Λ ∧ β x ∈ Xsp G1) ↔ (x ∈ Λ ∧ x ∈ Xsp F1)
  exact and_congr (hΛ x) (hX x)

theorem ngx_iff {T T1 : D.host.E} {F : LFlag (VS D) D.R.rS T} {F1 : LFlag (VS D) D.R.rS T1}
    {G1 : LFlag (VS D) D.R.rS T1} {β : GV D} {Λ : LV D} (g : ℕ) (hΛ : ∀ x, β x ∈ Λ ↔ x ∈ Λ)
    (hF : ∀ x, β x ∈ Xsp F ↔ x ∈ Xsp F) (hX : ∀ x, β x ∈ Xsp G1 ↔ x ∈ Xsp F1) (x : (VS D).V) :
    β x ∈ NgX Λ g F G1 ↔ x ∈ NgX Λ g F F1 := by
  apply mem_iff_of_gmap
  have hL : Formalism.HermitianLatticesTheory.gmap β Λ = Λ := gmap_eq_of_iff hΛ
  unfold NgX
  rw [GlobalTheory.Unfold.Model.gmap_sup, GlobalTheory.Unfold.Model.gmap_sup, gmap_eq_of_iff (xlam_iff hΛ hF),
    gmap_eq_of_iff (xlam_iff hΛ hX)]
  congr 2
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_smul'']
  congr 1

end GlobalTheory.KeyGroup

namespace GlobalTheory.KeyGroup

variable {D : D7}

open Formalism.L2.SG.NGCut.NormalVectorPairings in
theorem adapt_flag {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {a : GV D} (ha : Adapt a F F) (j : ℕ) :
    ∀ x ∈ Xflag F j, a x ∈ Xflag F j := by
  intro x hx
  unfold Xflag FlagG.Xa at hx ⊢
  refine Submodule.span_induction (p := fun x _ => a x ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < j}))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have h := ha.2 (Fin.castSucc i)
    have hf : frame F (Fin.castSucc i) = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [hf] at h
    have hmem : F.fl.e i ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < j}) := Submodule.subset_span ⟨i, hi, rfl⟩
    have hle : Xflag F (Fin.castSucc i).val ≤ Submodule.span D.host.E (F.fl.e '' {i | i.1 < j}) :=
      Submodule.span_mono (Set.image_mono fun k (hk : k.1 < (Fin.castSucc i).val) => lt_trans hk hi)
    have e : a (F.fl.e i) = F.fl.e i + (a (F.fl.e i) - F.fl.e i) := by abel
    rw [e]; exact Submodule.add_mem _ hmem (hle h)
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx

open Formalism.L2.SG.NGCut.NormalVectorPairings in
theorem adapt_X {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {a : GV D} (ha : Adapt a F F) (x : (VS D).V) :
    a x ∈ Xsp F ↔ x ∈ Xsp F := by
  have h : ∀ x ∈ Xsp F, a x ∈ Xsp F := by rw [X_eq_Xflag]; exact adapt_flag F ha _
  exact ⟨fun hx => by simpa using symm_mem_of_mem a _ h _ hx, h x⟩

open Formalism.L2.SG.NGCut.NormalVectorPairings in

def flagLatticeAutomorphismGroup {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : LV D) : Subgroup (GV D) where
  carrier := Aut0 F Λ
  one_mem' := ⟨GlobalTheory.Unfold.Model.adapt_one F, GlobalTheory.Unfold.Model.gmap_one Λ⟩
  mul_mem' := by
    rintro a b ⟨⟨hai, haf⟩, haΛ⟩ ⟨⟨hbi, hbf⟩, hbΛ⟩
    refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem hai hbi, fun i => ?_⟩, by rw [GlobalTheory.Unfold.Model.gmap_mul, hbΛ, haΛ]⟩
    have e : (a * b) (frame F i) - frame F i = a (b (frame F i) - frame F i) + (a (frame F i) - frame F i) := by
      show a (b _) - _ = _; rw [map_sub]; abel
    rw [e]
    exact Submodule.add_mem _ (adapt_flag F ⟨hai, haf⟩ _ _ (hbf i)) (haf i)
  inv_mem' := by
    rintro a ⟨⟨hai, haf⟩, haΛ⟩
    refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hai, fun i => ?_⟩, ?_⟩
    · have e : a⁻¹ (frame F i) - frame F i = -(a.symm (a (frame F i) - frame F i)) := by
        show a.symm _ - _ = _; rw [map_sub]; simp
      rw [e]
      exact Submodule.neg_mem _ (symm_mem_of_mem a _ (adapt_flag F ⟨hai, haf⟩ _) _ (haf i))
    · conv_lhs => rw [← haΛ]
      rw [← GlobalTheory.Unfold.Model.gmap_mul, inv_mul_cancel, GlobalTheory.Unfold.Model.gmap_one]

theorem one_mem_nrat {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : GV D) ∈ NRat F :=
  ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _,
    fun x _ => by show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _⟩

open Formalism.L2.SG.NGCut.NormalVectorPairings in

theorem nrat_conj {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {Λ : LV D} {a n : GV D} (ha : a ∈ Aut0 F Λ)
    (hn : n ∈ NRat F) : a * n * a⁻¹ ∈ NRat F := by
  obtain ⟨⟨hai, haf⟩, -⟩ := ha
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hai hn.1) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hai),
    fun j x hx => ?_, fun x hx => ?_⟩
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      show a (n (a.symm x)) - x = _; rw [map_sub, LinearEquiv.apply_symm_apply]
    rw [e]
    exact adapt_flag F ⟨hai, haf⟩ j _ (hn.2.1 j _ (symm_mem_of_mem a _ (adapt_flag F ⟨hai, haf⟩ (j + 1)) x hx))
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      show a (n (a.symm x)) - x = _; rw [map_sub, LinearEquiv.apply_symm_apply]
    rw [e]
    have hx' : a.symm x ∈ orth (VS D) (Xsp F) :=
      (orth_iff hai (adapt_X F ⟨hai, haf⟩) (a.symm x)).1 (by simpa using hx)
    exact (adapt_X F ⟨hai, haf⟩ _).2 (hn.2.2 _ hx')

theorem mem_Xsp_mapLF {T' : D.host.E} (F0' : FlagG (VS D) D.R.rS T') {γ : GV D}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (v : (VS D).V) :
    v ∈ Xsp (mapLF γ (lf D F0')) ↔ γ.symm v ∈ Xsp (lf D F0') := by
  rw [Formalism.L2.SG.Pf.Act.Xsp_mapLF hγ F0', Submodule.mem_map_equiv]

end GlobalTheory.KeyGroup

namespace GlobalTheory.KeyGroup

variable {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F0' : FlagG (VS D) D.R.rS T') (Λ : LV D)

theorem keyEq_refl (γ : GV D) : KeyEq F (lf D F0') Λ γ γ := by
  refine ⟨⟨1, one_mem_nrat F, 1, one_mem_nrat _, by group⟩, ?_⟩
  rw [mul_inv_cancel]
  intro x' _ l _
  exact Iff.rfl

variable {F F0' Λ}

theorem iota_transport {F1 F2 G1 G2 : LFlag (VS D) D.R.rS T'} (g : ℕ) {a β : GV D}
    (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hΛ : ∀ x, a x ∈ Λ ↔ x ∈ Λ) (hF : ∀ x, a x ∈ Xsp F ↔ x ∈ Xsp F)
    (h1 : ∀ x, a x ∈ Xsp G1 ↔ x ∈ Xsp F1) (h2 : ∀ x, a x ∈ Xsp G2 ↔ x ∈ Xsp F2)
    (h : IotaCompat Λ F F1 F2 β g) : IotaCompat Λ F G1 G2 (a * β * a⁻¹) g := by
  intro x' hx' l hl
  have hy : a.symm x' ∈ Lrep Λ F1 := (lrep_iff hi hΛ h1 _).1 (by simpa using hx')
  have hm : a.symm l ∈ Lrep Λ F := (lrep_iff hi hΛ hF _).1 (by simpa using hl)
  have k := h _ hy _ hm
  rw [← ngx_iff g hΛ hF h1 (a.symm l - a.symm x'), ← ngx_iff g hΛ hF h2 (a.symm l - β (a.symm x')),
    map_sub, map_sub] at k
  simp only [LinearEquiv.apply_symm_apply] at k
  exact k

theorem keyEq_transport {Λ' : LV D} {a a' γ₁ γ₂ : GV D} (ha : a ∈ Aut0 F Λ) (ha' : a' ∈ Aut0 (lf D F0') Λ')
    (h1 : γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : KeyEq F (lf D F0') Λ γ₁ γ₂) : KeyEq F (lf D F0') Λ (a * γ₁ * a'⁻¹) (a * γ₂ * a'⁻¹) := by
  obtain ⟨⟨n, hn, n', hn', e⟩, hι⟩ := h
  refine ⟨⟨a * n * a⁻¹, nrat_conj ha hn, a' * n' * a'⁻¹, nrat_conj ha' hn', by rw [e]; group⟩, ?_⟩
  have hai := ha.1.1
  have ha'i := ha'.1.1
  have hb : ∀ γ : GV D, γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      ∀ x, a x ∈ Xsp (mapLF (a * γ * a'⁻¹) (lf D F0')) ↔ x ∈ Xsp (mapLF γ (lf D F0')) := by
    intro γ hγ x
    have hγ' : a * γ * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
      (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hai hγ) ((Formalism.HermitianLatticesTheory.isom _).inv_mem ha'i)
    rw [mem_Xsp_mapLF F0' hγ', mem_Xsp_mapLF F0' hγ]
    have e1 : (a * γ * a'⁻¹).symm (a x) = a' (γ.symm x) := by
      rw [LinearEquiv.symm_apply_eq]; show a x = a (γ (a'.symm (a' (γ.symm x)))); simp
    rw [e1]
    exact adapt_X _ ha'.1 _
  have eβ : a * γ₂ * a'⁻¹ * (a * γ₁ * a'⁻¹)⁻¹ = a * (γ₂ * γ₁⁻¹) * a⁻¹ := by group
  rw [eβ]
  exact iota_transport (gS D) hai (mem_iff_of_gmap ha.2) (adapt_X F ha.1) (hb γ₁ h1) (hb γ₂ h2) hι

theorem pair_lrep {Λ' : LV D} {γ₁ γ₂ : GV D} (h1 : γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hΛ1 : Formalism.HermitianLatticesTheory.gmap γ₁ Λ' = Λ) (hΛ2 : Formalism.HermitianLatticesTheory.gmap γ₂ Λ' = Λ)
    (x : (VS D).V) :
    (γ₂ * γ₁⁻¹) x ∈ Lrep Λ (mapLF γ₂ (lf D F0')) ↔ x ∈ Lrep Λ (mapLF γ₁ (lf D F0')) := by
  have hi : γ₂ * γ₁⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom _).mul_mem h2 ((Formalism.HermitianLatticesTheory.isom _).inv_mem h1)
  refine lrep_iff hi (fun y => ?_) (fun y => ?_) x
  · show γ₂ (γ₁.symm y) ∈ Λ ↔ y ∈ Λ
    rw [mem_iff_of_gmap hΛ2, ← mem_iff_of_gmap hΛ1, LinearEquiv.apply_symm_apply]
  · rw [mem_Xsp_mapLF F0' h2, mem_Xsp_mapLF F0' h1]
    show γ₂.symm (γ₂ (γ₁.symm y)) ∈ _ ↔ _
    rw [LinearEquiv.symm_apply_apply]

theorem keyEq_symm {Λ' : LV D} {γ₁ γ₂ : GV D} (h1 : γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hΛ1 : Formalism.HermitianLatticesTheory.gmap γ₁ Λ' = Λ) (hΛ2 : Formalism.HermitianLatticesTheory.gmap γ₂ Λ' = Λ)
    (h : KeyEq F (lf D F0') Λ γ₁ γ₂) : KeyEq F (lf D F0') Λ γ₂ γ₁ := by
  obtain ⟨⟨n, hn, n', hn', e⟩, hι⟩ := h
  refine ⟨⟨n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F hn, n'⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn',
    by rw [e]; group⟩, ?_⟩
  intro x hx l hl
  have hy : (γ₂ * γ₁⁻¹) ((γ₁ * γ₂⁻¹) x) = x := by
    show γ₂ (γ₁.symm (γ₁ (γ₂.symm x))) = x; simp
  have hy' : (γ₁ * γ₂⁻¹) x ∈ Lrep Λ (mapLF γ₁ (lf D F0')) :=
    (pair_lrep h1 h2 hΛ1 hΛ2 _).1 (by rw [hy]; exact hx)
  have k := hι _ hy' l hl
  rw [hy] at k
  exact k.symm

theorem keyEq_trans {Λ' : LV D} {γ₁ γ₂ γ₃ : GV D} (h1 : γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hΛ1 : Formalism.HermitianLatticesTheory.gmap γ₁ Λ' = Λ) (hΛ2 : Formalism.HermitianLatticesTheory.gmap γ₂ Λ' = Λ)
    (k1 : KeyEq F (lf D F0') Λ γ₁ γ₂) (k2 : KeyEq F (lf D F0') Λ γ₂ γ₃) : KeyEq F (lf D F0') Λ γ₁ γ₃ := by
  obtain ⟨⟨n, hn, n', hn', e1⟩, hι1⟩ := k1
  obtain ⟨⟨m, hm, m', hm', e2⟩, hι2⟩ := k2
  refine ⟨⟨m * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F hm hn, n' * m',
    Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hn' hm', by rw [e2, e1]; group⟩, ?_⟩
  intro x' hx' l hl
  have hy := (pair_lrep h1 h2 hΛ1 hΛ2 x').2 hx'
  have a1 := hι1 x' hx' l hl
  have a2 := hι2 _ hy l hl
  have e : (γ₃ * γ₂⁻¹) ((γ₂ * γ₁⁻¹) x') = (γ₃ * γ₁⁻¹) x' := by
    show γ₃ (γ₂.symm (γ₂ (γ₁.symm x'))) = γ₃ (γ₁.symm x'); simp
  rw [e] at a2
  exact a1.trans a2

end GlobalTheory.KeyGroup

namespace GlobalTheory.KeyGroup

variable {D : D7} {T T' : D.host.E} {F : LFlag (VS D) D.R.rS T} {F0' : FlagG (VS D) D.R.rS T'} {Λ : LV D}

open Formalism.L2.SG.NGCut.NormalVectorPairings in

theorem keyEq_left {γ n : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hn : n ∈ NLam Λ F) :
    KeyEq F (lf D F0') Λ γ (n * γ) := by
  have hni : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1.1
  have hnΛ : ∀ x, n x ∈ Λ ↔ x ∈ Λ := mem_iff_of_gmap hn.1.2
  have hnX' : ∀ x ∈ Xsp F, n x ∈ Xsp F := X_pres F hn.2.1
  have hnX : ∀ x, n x ∈ Xsp F ↔ x ∈ Xsp F :=
    fun x => ⟨fun h => by simpa using symm_mem_of_mem n _ hnX' _ h, hnX' x⟩
  have hn1 : ∀ x, n x ∈ Xsp (mapLF (n * γ) (lf D F0')) ↔ x ∈ Xsp (mapLF γ (lf D F0')) := by
    intro x
    rw [mem_Xsp_mapLF F0' ((Formalism.HermitianLatticesTheory.isom _).mul_mem hni hγ), mem_Xsp_mapLF F0' hγ]
    have e : (n * γ).symm (n x) = γ.symm x := by
      rw [LinearEquiv.symm_apply_eq]; show n x = n (γ (γ.symm x)); simp
    rw [e]
  refine ⟨⟨n, ⟨hni, hn.2.1, hn.2.2⟩, 1, one_mem_nrat _, by group⟩, ?_⟩
  rw [mul_inv_cancel_right]
  intro x' _ l hl
  have hd : n.symm l - l ∈ NgX Λ (gS D) F (mapLF γ (lf D F0')) := by
    apply Submodule.mem_sup_left
    apply Submodule.mem_sup_right
    have hlo : n.symm l ∈ orth (VS D) (Xsp F) := (orth_iff hni hnX _).1 (by simpa using hl.2)
    have h3 := hn.2.2 _ hlo
    rw [LinearEquiv.apply_symm_apply] at h3
    refine ⟨Λ.sub_mem ((hnΛ _).1 (by simpa using hl.1)) hl.1, ?_⟩
    show n.symm l - l ∈ Xsp F
    rw [← neg_sub]; exact Submodule.neg_mem _ h3
  have e : l - n x' = n (n.symm l - x') := by rw [map_sub]; simp
  rw [e, ngx_iff (gS D) hnΛ hnX hn1, show n.symm l - x' = (l - x') + (n.symm l - l) by abel,
    Submodule.add_mem_iff_left _ hd]

theorem keyEq_right {Λ' : LV D} {γ m : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hγΛ : Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ) (hm : m ∈ NLam Λ' (lf D F0')) :
    KeyEq F (lf D F0') Λ γ (γ * m) := by
  have hmi : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hm.1.1
  have hmX' : ∀ x ∈ Xsp (lf D F0'), m x ∈ Xsp (lf D F0') := Formalism.L2.SG.NGCut.NormalVectorPairings.X_pres _ hm.2.1
  have hXeq : Xsp (mapLF (γ * m) (lf D F0')) = Xsp (mapLF γ (lf D F0')) := by
    ext v
    rw [mem_Xsp_mapLF F0' ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hmi), mem_Xsp_mapLF F0' hγ]
    have e : (γ * m).symm v = m.symm (γ.symm v) := by
      rw [LinearEquiv.symm_apply_eq]; show v = γ (m (m.symm (γ.symm v))); simp
    rw [e]
    exact ⟨fun h => by simpa using hmX' _ h,
      fun h => Formalism.L2.SG.NGCut.NormalVectorPairings.symm_mem_of_mem m _ hmX' _ h⟩
  have hNeq : NgX Λ (gS D) F (mapLF (γ * m) (lf D F0')) = NgX Λ (gS D) F (mapLF γ (lf D F0')) := by
    unfold NgX XLam; rw [hXeq]
  refine ⟨⟨1, one_mem_nrat _, m, ⟨hmi, hm.2.1, hm.2.2⟩, by group⟩, ?_⟩
  intro x' hx' l _
  rw [hNeq]
  have hU : ∀ x, γ x ∈ Xsp (mapLF γ (lf D F0')) ↔ x ∈ Xsp (lf D F0') := fun x => by
    rw [mem_Xsp_mapLF F0' hγ]; simp
  have hyΛ : γ.symm x' ∈ Λ' := (mem_iff_of_gmap hγΛ _).1 (by simpa using hx'.1)
  have hyo : γ.symm x' ∈ orth (VS D) (Xsp (lf D F0')) := (orth_iff hγ hU _).1 (by simpa using hx'.2)
  have hw : γ (m (γ.symm x') - γ.symm x') ∈ NgX Λ (gS D) F (mapLF γ (lf D F0')) := by
    apply Submodule.mem_sup_right
    refine ⟨(mem_iff_of_gmap hγΛ _).2 (Λ'.sub_mem ((mem_iff_of_gmap hm.1.2 _).2 hyΛ) hyΛ), ?_⟩
    show _ ∈ Xsp (mapLF γ (lf D F0'))
    exact (hU _).2 (hm.2.2 _ hyo)
  have e : (γ * m * γ⁻¹) x' = x' + γ (m (γ.symm x') - γ.symm x') := by
    show γ (m (γ.symm x')) = _; rw [map_sub]; simp
  rw [e, show l - (x' + γ (m (γ.symm x') - γ.symm x')) = (l - x') - γ (m (γ.symm x') - γ.symm x') by abel,
    Submodule.sub_mem_iff_left _ hw]

end GlobalTheory.KeyGroup

namespace GlobalTheory.KeyGroup

theorem keyStab_subgroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'),
    ∃ B : Subgroup (GV D × GV D), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧
      b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧
      KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) ∧
    (∀ n ∈ NLam t.lam (lf D (X.Fu u)), ∀ n' ∈ NLam t.lam' (lf D (X.Fu u')), (n, n') ∈ B) ∧
    ∀ a₁ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a₂ ∈ Aut0 (lf D (X.Fu u)) t.lam,
      ∀ a₁' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∀ a₂' ∈ Aut0 (lf D (X.Fu u')) t.lam',
      (KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam (a₁ * t.lin * a₁'⁻¹) (a₂ * t.lin * a₂'⁻¹) ↔
        (a₁⁻¹ * a₂, a₁'⁻¹ * a₂') ∈ B) := by
  intro D X Y u u' t
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hS : ∀ b₁ ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ b₂ ∈ Aut0 (lf D (X.Fu u')) t.lam',
      b₁ * t.lin * b₂⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap (b₁ * t.lin * b₂⁻¹) t.lam' = t.lam := by
    intro b₁ h₁ b₂ h₂
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem h₁.1.1 hγ) ((Formalism.HermitianLatticesTheory.isom _).inv_mem h₂.1.1), ?_⟩
    have h₂' : b₂⁻¹ ∈ Aut0 (lf D (X.Fu u')) t.lam' := (flagLatticeAutomorphismGroup _ _).inv_mem h₂
    rw [GlobalTheory.Unfold.Model.gmap_mul, GlobalTheory.Unfold.Model.gmap_mul, h₂'.2, hγΛ, h₁.2]
  let B : Subgroup (GV D × GV D) :=
  { carrier := {b | b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧
      KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)}
    one_mem' := ⟨(flagLatticeAutomorphismGroup _ _).one_mem, (flagLatticeAutomorphismGroup _ _).one_mem, by
      show KeyEq _ _ _ t.lin (1 * t.lin * 1⁻¹)
      rw [inv_one, one_mul, mul_one]; exact keyEq_refl _ _ _ _⟩
    mul_mem' := by
      rintro ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨hb₁, hb₂, kb⟩ ⟨hc₁, hc₂, kc⟩
      refine ⟨(flagLatticeAutomorphismGroup _ _).mul_mem hb₁ hc₁, (flagLatticeAutomorphismGroup _ _).mul_mem hb₂ hc₂, ?_⟩
      show KeyEq _ _ _ t.lin (b₁ * c₁ * t.lin * (b₂ * c₂)⁻¹)
      have k := keyEq_transport hb₁ hb₂ hγ (hS c₁ hc₁ c₂ hc₂).1 kc
      have e : b₁ * (c₁ * t.lin * c₂⁻¹) * b₂⁻¹ = b₁ * c₁ * t.lin * (b₂ * c₂)⁻¹ := by group
      rw [e] at k
      exact keyEq_trans hγ (hS b₁ hb₁ b₂ hb₂).1 hγΛ (hS b₁ hb₁ b₂ hb₂).2 kb k
    inv_mem' := by
      rintro ⟨b₁, b₂⟩ ⟨hb₁, hb₂, kb⟩
      have hi₁ : b₁⁻¹ ∈ Aut0 (lf D (X.Fu u)) t.lam := (flagLatticeAutomorphismGroup _ _).inv_mem hb₁
      have hi₂ : b₂⁻¹ ∈ Aut0 (lf D (X.Fu u')) t.lam' := (flagLatticeAutomorphismGroup _ _).inv_mem hb₂
      refine ⟨hi₁, hi₂, ?_⟩
      show KeyEq _ _ _ t.lin (b₁⁻¹ * t.lin * b₂⁻¹⁻¹)
      have k := keyEq_transport hi₁ hi₂ hγ (hS b₁ hb₁ b₂ hb₂).1 kb
      have e : b₁⁻¹ * (b₁ * t.lin * b₂⁻¹) * b₂⁻¹⁻¹ = t.lin := by group
      rw [e] at k
      exact keyEq_symm (hS _ hi₁ _ hi₂).1 hγ (hS _ hi₁ _ hi₂).2 hγΛ k }
  refine ⟨B, fun b => Iff.rfl, ?_, ?_⟩
  · intro n hn n' hn'
    have ha := GlobalTheory.Unfold.Model.unitriangular_lattice_stabiliser_sub_frame_automorphisms _ _ hn
    have ha' := GlobalTheory.Unfold.Model.unitriangular_lattice_stabiliser_sub_frame_automorphisms _ _ hn'
    refine ⟨ha, ha', ?_⟩
    show KeyEq _ _ _ t.lin (n * t.lin * n'⁻¹)
    have hinv : n'⁻¹ ∈ NLam t.lam' (lf D (X.Fu u')) := Formalism.L2.SG.Pf.nlam_inv hn'
    have k1 := keyEq_right (F := lf D (X.Fu u)) hγ hγΛ hinv
    have h2 := hS 1 (flagLatticeAutomorphismGroup _ _).one_mem n' ha'
    rw [one_mul] at h2
    have k2 := keyEq_left (F0' := X.Fu u') h2.1 hn
    rw [← mul_assoc] at k2
    exact keyEq_trans hγ h2.1 hγΛ h2.2 k1 k2
  · intro a₁ h₁ a₂ h₂ a₁' h₁' a₂' h₂'
    have hm : a₁⁻¹ * a₂ ∈ Aut0 (lf D (X.Fu u)) t.lam := (flagLatticeAutomorphismGroup _ _).mul_mem ((flagLatticeAutomorphismGroup _ _).inv_mem h₁) h₂
    have hm' : a₁'⁻¹ * a₂' ∈ Aut0 (lf D (X.Fu u')) t.lam' :=
      (flagLatticeAutomorphismGroup _ _).mul_mem ((flagLatticeAutomorphismGroup _ _).inv_mem h₁') h₂'
    constructor
    · intro k
      refine ⟨hm, hm', ?_⟩
      show KeyEq _ _ _ t.lin (a₁⁻¹ * a₂ * t.lin * (a₁'⁻¹ * a₂')⁻¹)
      have k' := keyEq_transport ((flagLatticeAutomorphismGroup _ _).inv_mem h₁) ((flagLatticeAutomorphismGroup _ _).inv_mem h₁') (hS _ h₁ _ h₁').1
        (hS _ h₂ _ h₂').1 k
      have e1 : a₁⁻¹ * (a₁ * t.lin * a₁'⁻¹) * a₁'⁻¹⁻¹ = t.lin := by group
      have e2 : a₁⁻¹ * (a₂ * t.lin * a₂'⁻¹) * a₁'⁻¹⁻¹ = a₁⁻¹ * a₂ * t.lin * (a₁'⁻¹ * a₂')⁻¹ := by group
      rw [e1, e2] at k'
      exact k'
    · intro hk
      obtain ⟨-, -, k⟩ := hk
      have k0 : KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (a₁⁻¹ * a₂ * t.lin * (a₁'⁻¹ * a₂')⁻¹) := k
      have k' := keyEq_transport h₁ h₁' hγ (hS _ hm _ hm').1 k0
      have e2 : a₁ * (a₁⁻¹ * a₂ * t.lin * (a₁'⁻¹ * a₂')⁻¹) * a₁'⁻¹ = a₂ * t.lin * a₂'⁻¹ := by group
      rw [e2] at k'
      exact k'

end GlobalTheory.KeyGroup
