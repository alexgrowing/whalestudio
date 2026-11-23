import Development.EtaleCohomology.WeilConjectures.LocalVanCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV.GluePf
open LateralTheory.EWeil LateralTheory.EWeil.Gys LateralTheory.EWeil.Gys.LV

def Sig : Prop := ∀ (l r : ℕ) (P : SPair l r) {T : Type} (Q : T → SPair l r) (g : ∀ t, (Q t).Hom P),
  ∃ (P' : SPair l r) (f : P'.Hom P) (a : ∀ t, (Q t).Hom P'), (∀ t, (a t).fX ≫ f.fX = (g t).fX) ∧
    Nonempty (IsColimit (Cofan.mk P'.X fun t => (a t).fX)) ∧ Nonempty (IsColimit (Cofan.mk P'.U fun t => (a t).fU)) ∧
    ((∀ x : P.X, ∃ t, x ∈ Set.range (g t).fX) → Surjective f.fX)

def ShvSigma : Prop := ∀ (R : Type) [CommRing R] (F : GlobalTheory.EtC.Shv R) {T : Type} {Y : T → Scheme.{0}} (c : Cofan Y), IsColimit c →
  Function.Bijective (fun (s : GlobalTheory.EtC.Sec F c.pt) (t : T) => GlobalTheory.EtC.Sec.res (c.inj t) s)

theorem glue_of (hS : Sig) (hF : ShvSigma) : Glue := by
  intro l _ r P c i n x hx
  choose Q g ht hz using hx
  obtain ⟨P', f, a, hfa, ⟨hX⟩, ⟨hU⟩, hsurj⟩ := hS l r P Q g
  refine ⟨P', f, hsurj fun t => ⟨t, ht t⟩, ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H z => ?_
  have key : ∀ t, ∃ y : SecI (l ^ c) i (Q t).X (n - 1), resA (l ^ c) i (Q t).j (n - 1) y = 0 ∧
      dA (l ^ c) i (Q t).X (n - 1) n y = resA (l ^ c) i (g t).fX n z.1 := by
    intro t
    have h := hz t
    unfold pullZ at h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
    obtain ⟨y, hy, e⟩ := h
    exact ⟨y, hy, e⟩
  choose y hy hd using key
  obtain ⟨Y, hY⟩ := (hF _ ((res _ (tw (l ^ c) i)).X (n - 1)) _ hX).2 y
  have hYt : ∀ t, resA (l ^ c) i (a t).fX (n - 1) Y = y t := fun t => congrFun hY t
  unfold pullZ
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  refine ⟨Y, ?_, ?_⟩
  · show resA (l ^ c) i P'.j (n - 1) Y = 0
    apply (hF _ ((res _ (tw (l ^ c) i)).X (n - 1)) _ hU).1
    funext t
    change resA (l ^ c) i (a t).fU (n - 1) (resA (l ^ c) i P'.j (n - 1) Y) = resA (l ^ c) i (a t).fU (n - 1) 0
    rw [map_zero, ← resA_comp, (a t).sqU, resA_comp, hYt, hy]
  · show dA (l ^ c) i P'.X (n - 1) n Y = resA (l ^ c) i f.fX n z.1
    apply (hF _ ((res _ (tw (l ^ c) i)).X n) _ hX).1
    funext t
    change resA (l ^ c) i (a t).fX n (dA (l ^ c) i P'.X (n - 1) n Y) = resA (l ^ c) i (a t).fX n (resA (l ^ c) i f.fX n z.1)
    rw [resA_dA, hYt, hd, ← resA_comp, hfa]

end LateralTheory.EWeil.Gys.LV.GluePf
