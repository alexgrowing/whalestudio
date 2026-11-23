import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.LatticeComparisonCompatible
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOf

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms NumberField

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf) (Mi : Submodule O (FnP P α))

theorem span_image_of_surj {V : Type} [AddCommGroup V] [Module LL V] (cmp : V →ₛₗ[e] FnP P α) (A : Subring LL)
    (hA : ∀ a ∈ A, e a ∈ Set.range (algebraMap O Kf)) (S : Set V)
    (hsurj : ∀ F ∈ Mi, RatFnP P α e F → ∃ x, cmp x = F)
    (hlat : ∀ x, cmp x ∈ Mi ↔ x ∈ Submodule.span A S) (hd : MRatSpan P α e Mi) :
    Submodule.span O (cmp '' S) = Mi := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (hlat s).mpr (Submodule.subset_span hs)
  · have key : ∀ v ∈ Submodule.span A S, cmp v ∈ Submodule.span O (cmp '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨o, ho⟩ := hA a a.2
        have h1 : cmp (a • x) = o • cmp x := by
          rw [show a • x = (a : LL) • x from rfl, LinearMap.map_smulₛₗ, ← ho, algebraMap_smul]
        rw [h1]
        exact Submodule.smul_mem _ o hx
    rw [← hd, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ := hsurj _ hx (cmpF_rat P α e Mi x)
    rw [← hv]
    exact key v ((hlat v).mp (by rw [hv]; exact hx))

end Gen

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

structure CmpHypR (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where
  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y
  uniq : ∀ u w hg, ValUniq ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y
  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))
  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  inj : ∀ u w hg, Function.Injective (cmpRec T Gt I u w hg)

  surj : ∀ u w hg, ∀ F ∈ (D.gat u w hg).M, RatFn (D.gat u w hg) (I.embW u w hg) F → ∃ x, cmpRec T Gt I u w hg x = F

  lat : ∀ u w hg x, cmpRec T Gt I u w hg x ∈ (D.gat u w hg).M ↔ x ∈ locW D.what₂.places w ((D.fm u).lat 0).L

  desc : ∀ u w hg, MRatSpan (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M

theorem cmpRec_rat (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : ((D.fm u).lat 0).V) :
    RatFn (D.gat u w hg) (I.embW u w hg) (cmpRec T Gt I u w hg x) := by
  intro i L
  unfold cmpRec cmpC
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, map_zero _⟩

theorem CmpHypR.hyp {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (H : CmpHypR T Gt I) :
    CmpHyp T Gt I where
  ex := H.ex
  uniq := H.uniq
  pos := H.pos
  chi := H.chi
  li := fun u w hg =>
    li_of_rat (I.embW u w hg) (evG (D.gat u w hg))
      (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).toAddMonoidHom (evG_sep _)
      (fun a x => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).map_smulₛₗ a x)
      (fun x => (ratFn_iff _ _ _).1 (cmpRec_rat T Gt I u w hg x)) (H.inj u w hg) _
      ((D.fm u).lat 0).b.linearIndependent
  latM := fun u w hg =>
    span_image_of_surj (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M
      (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)) (intW D.what₂.places w)
      (fun a ha => (I.embW_int u w hg a).1 ha) _ (H.surj u w hg) (H.lat u w hg) (H.desc u w hg)

end Formalism.L2.G.Cmp
