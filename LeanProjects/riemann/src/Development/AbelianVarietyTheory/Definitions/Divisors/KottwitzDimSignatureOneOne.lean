import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullCompOfEq

noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}

theorem infUniv_of_rep {X : Scheme.{0}} {s : X ⟶ Sp (D.OEp p)} (univ : Obj D p N s)
    (h : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (D.OEp p)) (o : Obj D p N s'),
      ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)) : InfUniv univ := by
  intro C C₀ _ _ _ _ π _ _ t o o₀ x₀ hx₀ ⟨m⟩ h₀
  obtain ⟨x, ⟨hx, ⟨mx⟩⟩, hu⟩ := h _ t o
  obtain ⟨y, -, hy⟩ := h _ _ o₀
  refine ⟨x, ⟨?_, hx, ⟨mx⟩⟩, fun x' h' => hu x' h'.2⟩
  exact (hy _ ⟨by rw [Category.assoc, hx], ⟨m.comp mx⟩⟩).trans (hy _ ⟨hx₀, h₀⟩).symm

theorem InfUniv.lift_point {X : Scheme.{0}} {s : X ⟶ Sp (D.OEp p)} {univ : Obj D p N s} (h : InfUniv univ)
    (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (t : Sp C ⟶ Sp (D.OEp p))
    (hl : ∀ o₀ : Obj D p N (spMap π ≫ t), ∃ o : Obj D p N t, Nonempty (ObjMap o₀ o (spMap π)))
    (x₀ : Sp C₀ ⟶ X) (hx₀ : x₀ ≫ s = spMap π ≫ t) : ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t := by
  have : ∃ o₀ : Obj D p N (spMap π ≫ t), Nonempty (ObjMap o₀ univ x₀) :=
    hx₀ ▸ Pull.exists_objMap F D p N _ _ s univ x₀
  obtain ⟨o₀, h₀⟩ := this
  obtain ⟨o, ho⟩ := hl o₀
  obtain ⟨x, hx, -⟩ := h C C₀ π hπ hsq t o o₀ x₀ hx₀ ho h₀
  exact ⟨x, hx.1, hx.2.1⟩

theorem not_infUniv_const {k : Type} [Field k] {b : Sp k ⟶ Sp (D.OEp p)} (o : Obj D p N b)
    (u : Obj D p N (spMap (algebraMap k (DualNumber k)) ≫ b))
    (m : ObjMap u o (spMap (algebraMap k (DualNumber k)))) : ¬ InfUniv u := by
  intro h
  let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  let j : k →+* DualNumber k := algebraMap k (DualNumber k)
  haveI : IsArtinianRing (DualNumber k) :=
    haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
    IsArtinianRing.of_finite k _
  have hs : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : RingHom.ker π ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have e1 : spMap π ≫ spMap j = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; rfl
  obtain ⟨o₀, h₀⟩ := Pull.exists_objMap F D p N _ _ _ u (spMap π)
  obtain ⟨x, -, hu⟩ := h (DualNumber k) k π hs hsq _ u o₀ (spMap π) rfl h₀ h₀
  have e2 : (spMap j ≫ spMap π) ≫ spMap j = spMap j := by rw [Category.assoc, e1, Category.comp_id]
  have a1 := hu (𝟙 _) ⟨Category.comp_id _, Category.id_comp _, ⟨ObjMap.refl u⟩⟩
  have a2 := hu (spMap j ≫ spMap π) ⟨by rw [← Category.assoc, e1, Category.id_comp],
    by rw [← Category.assoc, e2], objMap_cancel F D p N _ _ _ _ _ _ u u o _ _ m (e2.symm ▸ m)⟩
  have a3 : 𝟙 _ = spMap j ≫ spMap π := a1.trans a2.symm
  rw [← Spec.map_comp, ← Spec.map_id] at a3
  have a4 := congrArg (fun f => (CommRingCat.Hom.hom f DualNumber.eps : DualNumber k).snd) (Spec.map_injective a3)
  simp [π, j] at a4

theorem exists_not_infUniv : ∃ (D : Datum HostModel.E21) (p : ℕ), Good HostModel.E21 p 5 ∧
    ∃ (s : Sp (DualNumber ℂ) ⟶ Sp (D.OEp p)) (u : Obj D p 5 s), ¬ InfUniv u := by
  obtain ⟨D, p, -, -, hg, o, -⟩ := exists_datum_good_obj
  obtain ⟨u, ⟨m⟩⟩ := Pull.exists_objMap _ D p 5 _ _ _ o (spMap (algebraMap ℂ (DualNumber ℂ)))
  exact ⟨D, p, hg, _, u, not_infUniv_const o u m⟩

end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

def ω₂ : LinearMap.BilinForm k (k × k) :=
  LinearMap.mk₂ k (fun x y => x.1 * y.2 - x.2 * y.1) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

def L₁ : Submodule k (k × k) := LinearMap.ker (LinearMap.snd k k k)

theorem mem_L₁ (x : k × k) : x ∈ L₁ k ↔ x.2 = 0 := Iff.rfl

theorem ksDim_plane : KSDim (Int.castRingHom (Module.End k (k × k))) (ω₂ k) (L₁ k) ⊥ 1 := by
  refine ⟨fun _ => LinearMap.inr k k k ∘ₗ LinearMap.fst k k k, fun _ => ⟨?_, ?_, ?_⟩, fun g _ => ?_⟩
  · intro a x _; simp [mem_L₁]
  · intro x hx; simp [(Submodule.mem_bot k).1 hx, mem_L₁]
  · rintro ⟨a, b⟩ hx ⟨c, d⟩ hy
    rw [mem_L₁] at hx hy; simp at hx hy; simp [ω₂, hx, hy, mul_comm]
  · refine ⟨fun _ => (g (1, 0)).2, ?_, fun c hc => ?_⟩
    · rintro ⟨a, b⟩ hx
      rw [mem_L₁] at hx; simp at hx; subst hx
      have : ((a, 0) : k × k) = a • (1, 0) := by simp
      rw [mem_L₁, this, map_smul]; simp; ring
    · have := hc (1, 0) rfl
      rw [mem_L₁] at this
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp at this
      exact (sub_eq_zero.1 this).symm

theorem ksDim_plane_fixed : KSDim (Int.castRingHom (Module.End k (k × k))) (ω₂ k) (L₁ k) (L₁ k) 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun g hg => ⟨Fin.elim0, fun x hx => by simpa using hg.2.1 x hx,
    fun _ _ => Subsingleton.elim _ _⟩⟩

def diag : (k × k) →+* Module.End k (k × k) := (Algebra.lmul k (k × k)).toRingHom

theorem ksDim_plane_cm : KSDim (diag k) (ω₂ k) (L₁ k) ⊥ 0 := by
  refine ⟨Fin.elim0, fun i => i.elim0, fun g hg => ⟨Fin.elim0, fun x hx => ?_, fun _ _ => Subsingleton.elim _ _⟩⟩
  have := hg.1 (1, 0) x hx
  obtain ⟨a, b⟩ := x
  rw [mem_L₁] at hx; simp at hx; subst hx
  rw [mem_L₁] at this ⊢
  simpa [diag] using this

theorem not_ksDim_plane_zero : ¬ KSDim (Int.castRingHom (Module.End k (k × k))) (ω₂ k) (L₁ k) ⊥ 0 :=
  fun h => absurd (KSDim.unique h (ksDim_plane k)) (by norm_num)

def ω₄ : LinearMap.BilinForm k (Fin 4 → k) :=
  LinearMap.mk₂ k (fun x y => x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)

def act₄ : (k × k) →+* Module.End k (Fin 4 → k) :=
  (Algebra.lmul k (Fin 4 → k)).toRingHom.comp
    (RingHom.pi ![RingHom.fst k k, RingHom.fst k k, RingHom.snd k k, RingHom.snd k k])

def F₄ : Submodule k (Fin 4 → k) := LinearMap.ker (LinearMap.proj 1) ⊓ LinearMap.ker (LinearMap.proj 2)

theorem mem_F₄ (x : Fin 4 → k) : x ∈ F₄ k ↔ x 1 = 0 ∧ x 2 = 0 := Iff.rfl

theorem act₄_apply (a : k × k) (x : Fin 4 → k) : act₄ k a x = ![a.1 * x 0, a.1 * x 1, a.2 * x 2, a.2 * x 3] := by
  funext i; fin_cases i <;> rfl

theorem kottwitzDim_signatureOneOne : KSDim (act₄ k) (ω₄ k) (F₄ k) ⊥ 1 := by
  let f : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
    LinearMap.pi ![0, LinearMap.proj 0, -LinearMap.proj 3, 0]
  have hf : ∀ x, f x = ![0, x 0, -x 3, 0] := fun x => by funext i; fin_cases i <;> rfl
  refine ⟨fun _ => f, fun _ => ⟨?_, ?_, ?_⟩, fun g hg => ?_⟩
  · intro a x _; simp [mem_F₄, hf, act₄_apply]
  · intro x hx; simp [(Submodule.mem_bot k).1 hx]
  · intro x hx y hy
    rw [mem_F₄] at hx hy; simp [ω₄, hf, hx, hy, mul_comm]
  · let e : Fin 4 → k := ![1, 0, 0, 0]
    let e' : Fin 4 → k := ![0, 0, 0, 1]
    have he : e ∈ F₄ k := ⟨rfl, rfl⟩
    have he' : e' ∈ F₄ k := ⟨rfl, rfl⟩
    have h1 := hg.1 (1, 0) e he
    have h2 := hg.1 (0, 1) e' he'
    have h3 := hg.2.2 e he e' he'
    have a1 : act₄ k (1, 0) e = e := by simp [act₄_apply, e]
    have a2 : act₄ k (0, 1) e' = e' := by simp [act₄_apply, e']
    rw [a1, mem_F₄] at h1
    rw [a2, mem_F₄] at h2
    simp [act₄_apply] at h1 h2
    have h3' : g e 1 + g e' 2 = 0 := by simpa [ω₄, e, e'] using h3
    refine ⟨fun _ => g e 1, fun x hx => ?_, fun c hc => ?_⟩
    · have : x = x 0 • e + x 3 • e' := by
        funext i; fin_cases i <;> simp [e, e', hx.1, hx.2, ((mem_F₄ k x).1 hx).1, ((mem_F₄ k x).1 hx).2]
      have hgx : g x = x 0 • g e + x 3 • g e' := by conv_lhs => rw [this, map_add, map_smul, map_smul]
      rw [mem_F₄, hgx]
      simp [hf, h1, h2]
      constructor
      · ring
      · linear_combination x 3 * h3'
    · have := (hc e he).1
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [hf, e] at this
      exact (sub_eq_zero.1 this).symm

end Examples

end GlobalTheory.UPel.Sm.Model
