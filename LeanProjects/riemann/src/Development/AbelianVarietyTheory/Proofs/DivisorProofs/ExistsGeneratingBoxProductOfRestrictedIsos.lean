import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdBoxIso

section Ext

variable {B B₁ B₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂}

theorem gm_ext_g {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂') :
    gm ψ z ((extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂'))
        ((extLB M₁ M₂ b₁ b₂).g (extIdx a₁ a₂) (extIdx a₁' a₂')) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') := by
  have hm : ψ z ∈ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂') :=
    ⟨mem_extIdx h₁ h₂, mem_extIdx h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res ψ z _ hm _).trans ?_) ((gm_res ψ z _ hm _).trans ?_))
  · exact gm_pull_g M₁ b₁ ψ z (fun _ => a₁) (fun _ => a₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g M₂ b₂ ψ z (fun _ => a₂) (fun _ => a₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

theorem gm_ext_change {w : LB.Iso M (extLB M₁ M₂ b₁ b₂)} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z)
    (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (j j' : M.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂')
    (hj : ψ z ∈ M.U j) (hj' : ψ z ∈ M.U j') :
    gm ψ z _ (w.s (extIdx a₁ a₂, j)) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') * (gm ψ z _ (M.g j j'))⁻¹ *
        gm ψ z _ (w.s (extIdx a₁' a₂', j')) := by
  have hm : ψ z ∈ (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁ a₂, j) ⊓
      (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁' a₂', j') :=
    ⟨⟨mem_extIdx h₁ h₂, hj⟩, mem_extIdx h₁' h₂', hj'⟩
  have e := congrArg (gm ψ z _) (hw (extIdx a₁ a₂, j) (extIdx a₁' a₂', j'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M (extLB M₁ M₂ b₁ b₂) ψ z _ _ hm) (gm_res ψ z _ hm _))))
  rw [gm_ext_g ψ z a₁ a₁' a₂ a₂' h₁ h₁' h₂ h₂'] at e'
  exact e'

end Ext

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Sq

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂}

noncomputable def germ (p : T ⟶ B) (f : T ⟶ G) (h₁ : T ⟶ T₁) (h₂ : T ⟶ T₂) (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂))
    (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁))
    (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι)
    (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  (gm (r ≫ p) z _ (wM.s (extIdx a₁ a₂, jM)))⁻¹ * gw we₁ (r ≫ h₁) z a₁ (fun _ => n₁) *
    gw we₂ (r ≫ h₂) z a₂ (fun _ => n₂) * gm (r ≫ f) z _ (wL.s (extIdx n₁ n₂, jL))

variable {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem germ_change (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jM jM' : M.ι) (jL jL' : L.ι) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (n₁ n₁' : L₁.ι) (n₂ n₂' : L₂.ι)
    (cM : p (r z) ∈ M.U jM) (cM' : p (r z) ∈ M.U jM') (cL : f (r z) ∈ L.U jL) (cL' : f (r z) ∈ L.U jL')
    (c₁ : b₁ (p (r z)) ∈ M₁.U a₁) (c₁' : b₁ (p (r z)) ∈ M₁.U a₁')
    (c₂ : b₂ (p (r z)) ∈ M₂.U a₂) (c₂' : b₂ (p (r z)) ∈ M₂.U a₂')
    (d₁ : g₁ (f (r z)) ∈ L₁.U n₁) (d₁' : g₁ (f (r z)) ∈ L₁.U n₁')
    (d₂ : g₂ (f (r z)) ∈ L₂.U n₂) (d₂' : g₂ (f (r z)) ∈ L₂.U n₂') :
    germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ =
      gm (r ≫ p) z _ (M.g jM jM') * (gm (r ≫ f) z _ (L.g jL jL'))⁻¹ *
        germ p f h₁ h₂ wM wL we₁ we₂ r z jM' jL' a₁' a₂' n₁' n₂' := by
  have q₁ : p₁ (h₁ (r z)) = b₁ (p (r z)) := congrArg (fun g => g (r z)) eM₁.symm
  have q₂ : p₂ (h₂ (r z)) = b₂ (p (r z)) := congrArg (fun g => g (r z)) eM₂.symm
  have k₁ : f₁ (h₁ (r z)) = g₁ (f (r z)) := congrArg (fun g => g (r z)) eL₁.symm
  have k₂ : f₂ (h₂ (r z)) = g₂ (f (r z)) := congrArg (fun g => g (r z)) eL₂.symm
  have A := gm_ext_change hwM (r ≫ p) z a₁ a₁' a₂ a₂' jM jM' c₁ c₁' c₂ c₂' cM cM'
  have C := gm_ext_change hwL (r ≫ f) z n₁ n₁' n₂ n₂' jL jL' d₁ d₁' d₂ d₂' cL cL'
  have W₁ := hw₁ Z (r ≫ h₁) z a₁ a₁' (fun _ => n₁) (fun _ => n₁') (q₁ ▸ c₁) (q₁ ▸ c₁')
    (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁'))
  have W₂ := hw₂ Z (r ≫ h₂) z a₂ a₂' (fun _ => n₂) (fun _ => n₂') (q₂ ▸ c₂) (q₂ ▸ c₂')
    (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂'))
  rw [gm_pull_g L₁ f₁ (r ≫ h₁) z (fun _ => n₁) (fun _ => n₁') (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁')),
    Category.assoc, Category.assoc, ← eM₁, ← eL₁] at W₁
  rw [gm_pull_g L₂ f₂ (r ≫ h₂) z (fun _ => n₂) (fun _ => n₂') (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂')),
    Category.assoc, Category.assoc, ← eM₂, ← eL₂] at W₂
  rw [Category.assoc, Category.assoc] at A C
  unfold germ
  rw [A, C, W₁, W₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Sq

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Glue

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem exists_unit (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) (jM : M.ι) (jL : L.ι) :
    ∃ s : Γ(T, (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι),
        p (r z) ∈ M.U jM → f (r z) ∈ L.U jL → b₁ (p (r z)) ∈ M₁.U a₁ → b₂ (p (r z)) ∈ M₂.U a₂ →
        g₁ (f (r z)) ∈ L₁.U n₁ → g₂ (f (r z)) ∈ L₂.U n₂ →
        gm r z _ s = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ := by
  have q₁ : ∀ x, p₁ (h₁ x) = b₁ (p x) := fun x => congrArg (fun g => g x) eM₁.symm
  have q₂ : ∀ x, p₂ (h₂ x) = b₂ (p x) := fun x => congrArg (fun g => g x) eM₂.symm
  have k₁ : ∀ x, f₁ (h₁ x) = g₁ (f x) := fun x => congrArg (fun g => g x) eL₁.symm
  have k₂ : ∀ x, f₂ (h₂ x) = g₂ (f x) := fun x => congrArg (fun g => g x) eL₂.symm
  obtain ⟨W, hW⟩ : ∃ W : M₁.ι × M₂.ι × L₁.ι × L₂.ι → T.Opens, ∀ a x, x ∈ W a ↔
      (p x ∈ M.U jM ∧ f x ∈ L.U jL) ∧ (b₁ (p x) ∈ M₁.U a.1 ∧ b₂ (p x) ∈ M₂.U a.2.1) ∧
        (g₁ (f x) ∈ L₁.U a.2.2.1 ∧ g₂ (f x) ∈ L₂.U a.2.2.2) :=
    ⟨fun a => (p ⁻¹ᵁ M.U jM ⊓ f ⁻¹ᵁ L.U jL) ⊓ ((p ⁻¹ᵁ (b₁ ⁻¹ᵁ M₁.U a.1) ⊓ p ⁻¹ᵁ (b₂ ⁻¹ᵁ M₂.U a.2.1)) ⊓
      (f ⁻¹ᵁ (g₁ ⁻¹ᵁ L₁.U a.2.2.1) ⊓ f ⁻¹ᵁ (g₂ ⁻¹ᵁ L₂.U a.2.2.2))), fun _ _ => Iff.rfl⟩
  have l₀ : ∀ a, W a ≤ (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL) := fun a x hx =>
    ⟨mem_pull.2 ((hW a x).1 hx).1.1, mem_pull.2 ((hW a x).1 hx).1.2⟩
  have lM : ∀ a, W a ≤ p ⁻¹ᵁ ((LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a.1 a.2.1, jM)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.1.1 ((hW a x).1 hx).2.1.2, ((hW a x).1 hx).1.1⟩
  have lL : ∀ a, W a ≤ f ⁻¹ᵁ ((LB.div (extLB L₁ L₂ g₁ g₂) L).U (extIdx a.2.2.1 a.2.2.2, jL)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.2.1 ((hW a x).1 hx).2.2.2, ((hW a x).1 hx).1.2⟩
  have l₁ : ∀ a, W a ≤ h₁ ⁻¹ᵁ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => a.1, fun _ => a.2.2.1)) :=
    fun a x hx => ⟨mem_pull.2 ((q₁ x).symm ▸ ((hW a x).1 hx).2.1.1),
      mem_pull.2 ((k₁ x).symm ▸ ((hW a x).1 hx).2.2.1)⟩
  have l₂ : ∀ a, W a ≤ h₂ ⁻¹ᵁ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => a.2.1, fun _ => a.2.2.2)) :=
    fun a x hx => ⟨mem_pull.2 ((q₂ x).symm ▸ ((hW a x).1 hx).2.1.2),
      mem_pull.2 ((k₂ x).symm ▸ ((hW a x).1 hx).2.2.2)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(T, W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) a, r z ∈ W a →
      gm r z (W a) (u a) = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a.1 a.2.1 a.2.2.1 a.2.2.2 :=
    ⟨fun a => (res (lM a) (pullU p _ (wM.s (extIdx a.1 a.2.1, jM))))⁻¹ *
        res (l₁ a) (pullU h₁ _ (we₁.s (fun _ => a.1, fun _ => a.2.2.1))) *
        res (l₂ a) (pullU h₂ _ (we₂.s (fun _ => a.2.1, fun _ => a.2.2.2))) *
        res (lL a) (pullU f _ (wL.s (extIdx a.2.2.1 a.2.2.2, jL))),
      fun Z r z a hz => by
        simp only [map_mul, map_inv]
        rw [gm_res r z (lM a) hz, gm_pull r p z _ (lM a hz), gm_res r z (l₁ a) hz, gm_pull r h₁ z _ (l₁ a hz),
          gm_res r z (l₂ a) hz, gm_pull r h₂ z _ (l₂ a hz), gm_res r z (lL a) hz, gm_pull r f z _ (lL a hz)]
        rfl⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p x))
      obtain ⟨a₂, ha₂⟩ := exists_chart hM₂ (b₂ (p x))
      obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f x))
      obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, n₁, n₂),
        (hW _ x).2 ⟨⟨mem_pull.1 hx.1, mem_pull.1 hx.2⟩, ⟨ha₁, ha₂⟩, ⟨hn₁, hn₂⟩⟩⟩) u
    (fun a a' x hx => by
      have i := (hW a x).1 hx.1
      have i' := (hW a' x).1 hx.2
      have k := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ (𝟙 T) x jM jM jL jL a.1 a'.1 a.2.1 a'.2.1
        a.2.2.1 a'.2.2.1 a.2.2.2 a'.2.2.2 i.1.1 i.1.1 i.1.2 i.1.2 i.2.1.1 i'.2.1.1 i.2.1.2 i'.2.1.2
        i.2.2.1 i'.2.2.1 i.2.2.2 i'.2.2.2
      rw [gm_self hM (𝟙 T ≫ p) x i.1.1, gm_self hL (𝟙 T ≫ f) x i.1.2, inv_one, _root_.one_mul,
        _root_.one_mul] at k
      exact (hu _ (𝟙 T) x a hx.1).trans (k.trans (hu _ (𝟙 T) x a' hx.2).symm))
  refine ⟨s, fun Z r z a₁ a₂ n₁ n₂ cM cL c₁ c₂ d₁ d₂ => ?_⟩
  have hz := (hW (a₁, a₂, n₁, n₂) (r z)).2 ⟨⟨cM, cL⟩, ⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩
  exact (gm_res r z (l₀ _) hz s).symm.trans ((congrArg (gm r z (W _)) (hs _)).trans (hu Z r z _ hz))

end Glue

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

theorem exists_wiso : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → wM.IsGen → wL.IsGen → we₁.IsGen → we₂.IsGen → ∃ we : LB.Iso (L.pull f) (M.pull p), we.IsGen ∧ BoxSq wM wL we we₁ we₂ h₁ h₂ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  rw [isGen_iff] at hw₁ hw₂
  choose s hs using exists_unit (h₁ := h₁) (h₂ := h₂) hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  refine ⟨⟨fun q => s (q.1 PUnit.unit) (q.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z r z j j' k k' a₂ b₂' a₄ b₄
    obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p (r z)))
    obtain ⟨a₂', ha₂⟩ := exists_chart hM₂ (b₂ (p (r z)))
    obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f (r z)))
    obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f (r z)))
    have a₄' : f (r z) ∈ L.U (k PUnit.unit) := mem_pull.1 a₄
    have b₄' : f (r z) ∈ L.U (k' PUnit.unit) := mem_pull.1 b₄
    have c := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ r z j j' (k PUnit.unit) (k' PUnit.unit) a₁ a₁ a₂' a₂'
      n₁ n₁ n₂ n₂ a₂ b₂' a₄' b₄' ha₁ ha₁ ha₂ ha₂ hn₁ hn₁ hn₂ hn₂
    rw [← hs j _ Z r z a₁ a₂' n₁ n₂ a₂ a₄' ha₁ ha₂ hn₁ hn₂, ← hs j' _ Z r z a₁ a₂' n₁ n₂ b₂' b₄' ha₁ ha₂ hn₁ hn₂] at c
    rw [gm_pull_g L f r z k k' a₄ b₄]
    exact c
  · intro Z r z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
    have e := hs (J (r ≫ p)) (N (r ≫ f)) Z r z (J₁ ((r ≫ p) ≫ b₁)) (J₂ ((r ≫ p) ≫ b₂)) (N₁ ((r ≫ f) ≫ g₁))
      (N₂ ((r ≫ f) ≫ g₂)) (hJ _) (hN _) (hJ₁ _) (hJ₂ _) (hN₁ _) (hN₂ _)
    show om wM z J₁ J₂ J (r ≫ p) * gm r z _ (s (J (r ≫ p)) (N (r ≫ f))) = _
    rw [e]
    unfold germ om
    simp only [_root_.mul_assoc, mul_inv_cancel_left]

end GlobalTheory.ProdBoxIso
