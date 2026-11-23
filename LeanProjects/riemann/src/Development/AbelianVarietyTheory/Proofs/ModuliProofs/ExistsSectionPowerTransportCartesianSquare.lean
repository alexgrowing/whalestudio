import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SecMove

section General

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem exists_up_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (g : Y ⟶ Y') (a : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => (g ≫ φ' k) ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p → r z ∈ LB.wchart L' (fun k => g ≫ φ' k) q →
        gs r z (LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p) (s.f p) =
          (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w (fun k => g ≫ φ' k) ε p q
  have tr : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (q q' : K → L'.ι),
      trF φ' ε (r ≫ g) z q q' = trF (fun k => g ≫ φ' k) ε r z q q' := fun r z q q' => by
    simp only [trF, Category.assoc]
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p → r z ∈ LB.wchart L' (fun k => g ≫ φ' k) q →
      gs r z _ s = (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q =>
      LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p ⊓ LB.wchart L' (fun k => g ≫ φ' k) q
    have le : ∀ q, W q ≤ g ⁻¹ᵁ LB.wchart L' φ' q := fun q y hy =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (le q)).op).hom ((g.app _).hom (a.f q)),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz)))
          ((gs_res r z (le q) hz _).trans (gs_pull r g z _ (le q hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' ((g ≫ φ' k) y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, sec_trans a (𝟙 Y ≫ g) y (le q hy.1) (le q' hy.2), tr,
          pw_trans hw _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2, trF_self hL _ ε (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_comm])
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W q)) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' ((g ≫ φ' k) y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun k => g ≫ φ' k) q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw _ ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, _root_.mul_one, Units.val_mul,
    _root_.mul_assoc]
  rfl

def Rel (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (a : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q)

theorem exists_equiv (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) [IsIso h] (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) :
    ∃ e : LB.Sec (LB.LinComb L' φ' ε) ≃ LB.Sec (LB.LinComb L φ ε), ∀ a, Rel w φ' φ ε h a (e a) := by
  have H := fun s => GlobalTheory.SecPull.existsUnique_secPull X X' Y Y' L L' F hL hL' w hw K φ' φ ε h hc s
  choose d hd hd' using H
  obtain rfl : φ = fun k => (inv h ≫ φ' k) ≫ F := funext fun k => by
    rw [Category.assoc, hc, IsIso.inv_hom_id_assoc]
  have inj : Function.Injective d := fun s s' e => by
    have e : s.f = s'.f := funext fun p => fn_ext fun y hy => by
      choose q hq using fun k => exists_chart hL' (φ' k (inv h y))
      have h₁ := hd s _ (inv h) y p q (Set.mem_iInter.1 hy) hq
      have h₂ := hd s' _ (inv h) y p q (Set.mem_iInter.1 hy) hq
      rw [IsIso.inv_hom_id] at h₁ h₂
      rw [e] at h₁
      exact h₁.trans h₂.symm
    cases s; cases s'; cases e; rfl
  have surj : Function.Surjective d := fun a => by
    obtain ⟨s, hs⟩ := exists_up_sec ((isGen_iff w).1 hw) hL hL' φ' ε (inv h) a
    refine ⟨s, (hd' s a fun Z r z p q hp hq => ?_).symm⟩
    have e : ∀ k, (r ≫ h) ≫ inv h ≫ φ' k = r ≫ φ' k := fun k => by simp
    rw [hs Z (r ≫ h) z p q (Set.mem_iInter.2 fun k => by
        show F (((r ≫ h) ≫ inv h ≫ φ' k) z) ∈ L.U (p k)
        rw [e]; exact hp k) (Set.mem_iInter.2 fun k => by
        show ((r ≫ h) ≫ inv h ≫ φ' k) z ∈ L'.U (q k)
        rw [e]; exact hq k), Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [pw, e]
  refine ⟨(Equiv.ofBijective d ⟨inj, surj⟩).symm, fun a => ?_⟩
  have := hd ((Equiv.ofBijective d ⟨inj, surj⟩).symm a)
  rw [show d ((Equiv.ofBijective d ⟨inj, surj⟩).symm a) = a from (Equiv.ofBijective d ⟨inj, surj⟩).apply_symm_apply a]
    at this
  exact this

def LinAt {Y₁ Y₂ T Z : Scheme.{0}} (L : LB X) (N : ℤ) (σ₁ : Y₁ ⟶ X) (σ₂ : Y₂ ⟶ X) (m : Y₂ ⟶ Y₁) (π : Y₂ ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))) (c : Fin n → Γ(T, ⊤))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))) (r : Z ⟶ Y₂) (z : Z) (p : L.ι) : Prop :=
  gs r z (LB.wchart L (fun _ : Fin 1 => σ₂) (fun _ => p)) (s.f (fun _ => p)) =
    ∑ i, gs (r ≫ π) z ⊤ (c i) * gs (r ≫ m) z (LB.wchart L (fun _ : Fin 1 => σ₁) (fun _ => p)) ((b i).f (fun _ => p))

theorem val_iff {Y₁ Y₂ T : Scheme.{0}} (hL : L.IsLB) (N : ℤ) (σ₁ : Y₁ ⟶ X) (σ₂ : Y₂ ⟶ X) (m : Y₂ ⟶ Y₁) (π : Y₂ ⟶ T)
    (hm : m ≫ σ₁ = σ₂) {n : ℕ}
    (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))) (c : Fin n → Γ(T, ⊤))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))) :
    (∀ (z : Y₂) (J), Good L z J → sval s (𝟙 _) z J = ∑ i, gs π z ⊤ (c i) * sval (b i) m z J) ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) (p : L.ι), σ₂ (r z) ∈ L.U p → LinAt L N σ₁ σ₂ m π b c s r z p := by
  constructor
  · intro H Z r z p hp
    obtain ⟨J, hJ, e⟩ := exists_good L hL (r z) (fun _ : Fin 1 => σ₂) (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
    have := congrArg (r.stalkMap z).hom (H (r z) J hJ)
    rw [sval_of s _ _ J (fun _ => p) (fun k => by rw [Category.id_comp]; exact e k), map_sum] at this
    have e₀ := gs_comp r (𝟙 Y₂) z (LB.wchart L (fun _ : Fin 1 => σ₂) (fun _ => p)) (Set.mem_iInter.2 fun _ => hp)
      (s.f fun _ => p)
    rw [Category.comp_id] at e₀
    refine e₀.trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_mul, sval_of (b i) _ _ J (fun _ => p) (fun k => by rw [hm]; exact e k)]
    exact congrArg₂ (· * ·) (gs_comp r π z ⊤ trivial _).symm
      (gs_comp r m z (LB.wchart L (fun _ : Fin 1 => σ₁) (fun _ => p)) (Set.mem_iInter.2 fun _ => by
        show (m ≫ σ₁) (r z) ∈ L.U p
        rw [hm]; exact hp) _).symm
  · intro H z J hJ
    have := H _ (𝟙 _) z (J σ₂) (hJ σ₂)
    rw [LinAt, Category.id_comp, Category.id_comp] at this
    rw [sval_of s _ _ J (fun _ => J σ₂) (fun k => by rw [Category.id_comp])]
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [sval_of (b i) _ _ J (fun _ => J σ₂) (fun k => by rw [hm])]

theorem linAt_iff {Y₁ Y₂ T Y₁' Y₂' T' Z : Scheme.{0}} (w : LB.Iso L' (L.pull F)) (N : ℤ)
    {σ₁ : Y₁ ⟶ X} {σ₂ : Y₂ ⟶ X} {m : Y₂ ⟶ Y₁} {π : Y₂ ⟶ T}
    {σ₁' : Y₁' ⟶ X'} {σ₂' : Y₂' ⟶ X'} {m' : Y₂' ⟶ Y₁'} {π' : Y₂' ⟶ T'}
    {h₁ : Y₁' ⟶ Y₁} {h₂ : Y₂' ⟶ Y₂} {u : T' ⟶ T} (hm' : m' ≫ σ₁' = σ₂') (hh : m' ≫ h₁ = h₂ ≫ m)
    (hπ : π' ≫ u = h₂ ≫ π) {n : ℕ}
    {b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))} (c : Fin n → Γ(T, ⊤))
    {s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))}
    {b' : Fin n → LB.Sec (LB.LinComb L' (fun _ : Fin 1 => σ₁') (fun _ => N))}
    {s' : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => σ₂') (fun _ => N))}
    (hb : ∀ i, Rel w _ _ _ h₁ (b' i) (b i)) (hs : Rel w _ _ _ h₂ s' s) (r : Z ⟶ Y₂') (z : Z) (p : L.ι) (q : L'.ι)
    (hp : F (σ₂' (r z)) ∈ L.U p) (hq : σ₂' (r z) ∈ L'.U q) :
    LinAt L' N σ₁' σ₂' m' π' b' (fun i => u.appTop.hom (c i)) s' r z q ↔ LinAt L N σ₁ σ₂ m π b c s (r ≫ h₂) z p := by
  subst hm'
  have e₁ := hs Z r z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
  have e₂ := fun i => hb i Z (r ≫ m') z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
  have e₃ : pw w (fun _ : Fin 1 => σ₁') (fun _ => N) (r ≫ m') z (fun _ => p) (fun _ => q) =
      pw w (fun _ : Fin 1 => m' ≫ σ₁') (fun _ => N) r z (fun _ => p) (fun _ => q) := by
    simp only [pw, Category.assoc]
  have e₄ : ∀ i, gs (r ≫ π') z ⊤ (u.appTop.hom (c i)) = gs ((r ≫ h₂) ≫ π) z ⊤ (c i) := fun i =>
    (gs_pull (r ≫ π') u z ⊤ trivial (c i)).trans (by rw [Category.assoc, hπ, Category.assoc])
  have e₅ : (r ≫ h₂) ≫ m = (r ≫ m') ≫ h₁ := by rw [Category.assoc, ← hh, Category.assoc]
  unfold LinAt
  rw [e₁, e₅]
  simp only [e₂, e₃, e₄, mul_left_comm _ (Units.val _), ← Finset.mul_sum, Units.mul_right_inj]

end General

def totMap {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    (hp : IsPullback φ G'.hom G.hom f) {T' : Over Z'} {T : Over Z} (u : T'.left ≅ T.left)
    (hu : u.hom ≫ T.hom = T'.hom ≫ f) : (T' ⊗ G').left ⟶ (T ⊗ G).left :=
  pullback.lift ((fst T' G').left ≫ u.hom) ((snd T' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hu, hp.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w])

section
variable {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    (hp : IsPullback φ G'.hom G.hom f) {T' : Over Z'} {T : Over Z} (u : T'.left ≅ T.left)
    (hu : u.hom ≫ T.hom = T'.hom ≫ f)

theorem totMap_fst : totMap hp u hu ≫ (fst T G).left = (fst T' G').left ≫ u.hom := pullback.lift_fst _ _ _

theorem totMap_snd : totMap hp u hu ≫ (snd T G).left = (snd T' G').left ≫ φ := pullback.lift_snd _ _ _

theorem totMap_isIso : IsIso (totMap hp u hu) := by
  have p₁ : IsPullback (snd T' G').left (fst T' G').left G'.hom T'.hom := (IsPullback.of_hasPullback T'.hom G'.hom).flip
  have p₂ : IsPullback (snd T G).left (fst T G).left G.hom T.hom := (IsPullback.of_hasPullback T.hom G.hom).flip
  have p₃ := p₁.paste_horiz hp
  rw [← totMap_snd hp u hu, ← hu] at p₃
  have p₄ := IsPullback.of_right p₃ (totMap_fst hp u hu) p₂
  exact p₄.isIso_fst_of_isIso

end

theorem transport : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → ∀ N : ℕ, ∃ e : ∀ (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left), u.hom ≫ T.hom = T'.hom ≫ f → (LB.Sec (Out.LPow G' L' (N : ℤ) T') ≃ LB.Sec (Out.LPow G L (N : ℤ) T)), ∀ (T₁' T₂' : Over Z') (T₁ T₂ : Over Z) (u₁ : T₁'.left ≅ T₁.left) (u₂ : T₂'.left ≅ T₂.left) (h₁ : u₁.hom ≫ T₁.hom = T₁'.hom ≫ f) (h₂ : u₂.hom ≫ T₂.hom = T₂'.hom ≫ f) (k' : T₂' ⟶ T₁') (k : T₂ ⟶ T₁), k'.left ≫ u₁.hom = u₂.hom ≫ k.left → ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) T₁')) (c : Fin n → Γ(T₂.left, ⊤)) (s : LB.Sec (Out.LPow G' L' (N : ℤ) T₂')), GlobalTheory.LN.Lin G' L' N k' b (fun i => u₂.hom.appTop.hom (c i)) s ↔ GlobalTheory.LN.Lin G L N k (fun i => e T₁' T₁ u₁ h₁ (b i)) c (e T₂' T₂ u₂ h₂ s) := by
  intro Z Z' G G' f φ L L' hL hL' hp ⟨w, hw⟩ N
  have H := fun (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left) (hu : u.hom ≫ T.hom = T'.hom ≫ f) =>
    haveI := totMap_isIso hp u hu
    exists_equiv hL hL' w hw (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T G).left) (fun _ => (N : ℤ))
      (totMap hp u hu) (fun _ => (totMap_snd hp u hu).symm)
  choose e he using H
  refine ⟨e, fun T₁' T₂' T₁ T₂ u₁ u₂ h₁ h₂ k' k hk n b c s => ?_⟩
  have hm : (k ▷ G).left ≫ (snd T₁ G).left = (snd T₂ G).left := by rw [← Over.comp_left, whiskerRight_snd]
  have hm' : (k' ▷ G').left ≫ (snd T₁' G').left = (snd T₂' G').left := by rw [← Over.comp_left, whiskerRight_snd]
  have hf : (k ▷ G).left ≫ (fst T₁ G).left = (fst T₂ G).left ≫ k.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have hf' : (k' ▷ G').left ≫ (fst T₁' G').left = (fst T₂' G').left ≫ k'.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have hh : (k' ▷ G').left ≫ totMap hp u₁ h₁ = totMap hp u₂ h₂ ≫ (k ▷ G).left := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst T₁ G).left = (_ ≫ _) ≫ (fst T₁ G).left
      rw [Category.assoc, Category.assoc, totMap_fst, hf, reassoc_of% hf', hk, ← Category.assoc, ← Category.assoc,
        totMap_fst]
    · show (_ ≫ _) ≫ (snd T₁ G).left = (_ ≫ _) ≫ (snd T₁ G).left
      rw [Category.assoc, Category.assoc, totMap_snd, hm, reassoc_of% hm', totMap_snd]
  have key := fun (W : Scheme.{0}) (r : W ⟶ (T₂' ⊗ G').left) =>
    linAt_iff w (N : ℤ) hm' hh (totMap_fst hp u₂ h₂).symm c (fun i => he T₁' T₁ u₁ h₁ (b i)) (he T₂' T₂ u₂ h₂ s) r
  refine (val_iff hL' _ _ _ _ _ hm' b _ s).trans (Iff.trans ?_ (val_iff hL _ _ _ _ _ hm _ c _).symm)
  constructor
  · intro H W r z p hz
    haveI := totMap_isIso hp u₂ h₂
    obtain ⟨r', rfl⟩ : ∃ r', r = r' ≫ totMap hp u₂ h₂ := ⟨r ≫ inv (totMap hp u₂ h₂), by simp⟩
    obtain ⟨q, hq⟩ := exists_chart hL' ((snd T₂' G').left (r' z))
    refine (key W r' z p q ?_ hq).1 (H W r' z q hq)
    show ((snd T₂' G').left ≫ φ) (r' z) ∈ L.U p
    rw [← totMap_snd hp u₂ h₂]; exact hz
  · intro H W r z q hq
    obtain ⟨p, hz⟩ := exists_chart hL (φ ((snd T₂' G').left (r z)))
    refine (key W r z p q hz hq).2 (H W _ z p ?_)
    show (totMap hp u₂ h₂ ≫ (snd T₂ G).left) (r z) ∈ L.U p
    rw [totMap_snd]; exact hz

end GlobalTheory.SecMove
