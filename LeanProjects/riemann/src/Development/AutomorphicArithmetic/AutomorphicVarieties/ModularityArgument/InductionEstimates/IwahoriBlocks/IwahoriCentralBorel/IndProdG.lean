import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndSeed
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrCases

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

noncomputable section

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Tools

variable {G V Y H : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [Group H]

private theorem irrCases (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe20.irrCases ρ h W hW

private theorem irrOf (ρ : Representation ℂ G V) (hn : Nontrivial V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) : ρ.IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · rcases h S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · exact Or.inl (Subrepresentation.ext e)
    · exact Or.inr (Subrepresentation.ext e)

private theorem commY {A B : Type} [Group A] [Group B] (y : Representation ℂ (A × B) Y) (a : A) (b : B) (v : Y) :
    y (a, 1) (y (1, b) v) = y (1, b) (y (a, 1) v) := by
  have e1 : y (a, 1) (y (1, b) v) = y (a, b) v := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have e2 : y (1, b) (y (a, 1) v) = y (a, b) v := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [e1, e2]

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem smNhds (ρ : Representation ℂ G V) (v : V) (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) :
    v ∈ GlobalTheory.PRep.smoothPart ρ := by
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 v = v
        simp
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul]; simp }
  exact T.isOpen_of_mem_nhds (g := 1) h

private theorem indLaw {j : H →* G} {y : Representation ℂ H Y} {X : Submodule ℂ Y} {f : G → Y} (hf : f ∈ IndF j y X)
    (h : H) (g : G) : f (j h * g) = y h (f g) := (Submodule.mem_inf.1 hf).1.2 h g

private theorem indSm {j : H →* G} {y : Representation ℂ H Y} {X : Submodule ℂ Y} {f : G → Y} (hf : f ∈ IndF j y X) :
    {g : G | rightReg ℂ G Y g f = f} ∈ nhds (1 : G) :=
  IsOpen.mem_nhds (Submodule.mem_inf.1 hf).2 (by simp)

private theorem indMk {j : H →* G} {y : Representation ℂ H Y} {f : G → Y} (h1 : ∀ h g, f (j h * g) = y h (f g))
    (h2 : {g : G | rightReg ℂ G Y g f = f} ∈ nhds (1 : G)) : f ∈ IndF j y ⊤ :=
  Submodule.mem_inf.2 ⟨⟨fun _ => trivial, h1⟩, smNhds _ _ h2⟩

end Tools

section Trans

variable {G₁ G₂ H₁ H₂ Γ Y : Type} [Group G₁] [Group G₂] [Group H₁] [Group H₂] [AddCommGroup Y] [Module ℂ Y]
  [TopologicalSpace G₁] [IsTopologicalGroup G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

private theorem memTrans (e : G₁ ≃* G₂) (he : Continuous e) (j₁ : H₁ →* G₁) (j₂ : H₂ →* G₂) (eh : H₁ ≃* H₂)
    (hj : ∀ h, e (j₁ h) = j₂ (eh h)) (y₁ : Representation ℂ H₁ Y) (y₂ : Representation ℂ H₂ Y)
    (hy : ∀ h, y₁ h = y₂ (eh h)) {f : G₂ → Y} (hf : f ∈ IndF j₂ y₂ ⊤) : (fun x => f (e x)) ∈ IndF j₁ y₁ ⊤ := by
  refine indMk (fun h g => ?_) ?_
  · show f (e (j₁ h * g)) = y₁ h (f (e g))
    rw [map_mul, hj, indLaw hf, hy]
  · have hs : {g : G₂ | rightReg ℂ G₂ Y g f = f} ∈ nhds (e 1) := by
      rw [map_one]; exact indSm hf
    refine Filter.mem_of_superset (he.continuousAt.preimage_mem_nhds hs) ?_
    intro g hg
    funext x
    have := congrFun (show rightReg ℂ G₂ Y (e g) f = f from hg) (e x)
    show f (e (x * g)) = f (e x)
    rw [map_mul]
    exact this

private theorem simpleTrans (e : G₁ ≃* G₂) (he : Continuous e) (he' : Continuous e.symm) (j₁ : H₁ →* G₁) (j₂ : H₂ →* G₂)
    (eh : H₁ ≃* H₂) (hj : ∀ h, e (j₁ h) = j₂ (eh h)) (y₁ : Representation ℂ H₁ Y) (y₂ : Representation ℂ H₂ Y)
    (hy : ∀ h, y₁ h = y₂ (eh h)) (γ : Γ → Y →ₗ[ℂ] Y) (hS : SimpleG (IndF j₂ y₂ ⊤) γ) : SimpleG (IndF j₁ y₁ ⊤) γ := by
  have hback : ∀ {f : G₁ → Y}, f ∈ IndF j₁ y₁ ⊤ → (fun x => f (e.symm x)) ∈ IndF j₂ y₂ ⊤ := by
    intro f hf
    refine memTrans e.symm he' j₂ j₁ eh.symm (fun h => ?_) y₂ y₁ (fun h => ?_) hf
    · apply e.injective
      rw [MulEquiv.apply_symm_apply, hj, MulEquiv.apply_symm_apply]
    · rw [hy, MulEquiv.apply_symm_apply]
  intro Q hQ h1 h2
  let W : (G₂ → Y) →ₗ[ℂ] (G₁ → Y) := LinearMap.funLeft ℂ Y e
  have hWa : ∀ (f : G₂ → Y) x, W f x = f (e x) := fun _ _ => rfl
  have hup : ∀ f, W f ∈ Q → f ∈ IndF j₂ y₂ ⊤ := by
    intro f hf
    have := hback (hQ hf)
    have e' : (fun x => W f (e.symm x)) = f := by
      funext x; simp [hWa]
    rwa [e'] at this
  have hmem : ∀ f, W f ∈ Q → f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤ := fun f hf => Submodule.mem_inf.2 ⟨hf, hup f hf⟩
  have hsurj : ∀ φ : G₁ → Y, W (fun x => φ (e.symm x)) = φ := by
    intro φ; funext x; simp [hWa]
  have st1 : ∀ g, ∀ f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤, rightReg ℂ G₂ Y g f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤ := by
    intro g f hf
    refine hmem _ ?_
    have := h1 (e.symm g) _ (Submodule.mem_inf.1 hf).1
    convert this using 1
    funext x
    show f (e x * g) = f (e (x * e.symm g))
    simp
  have st2 : ∀ c, ∀ f ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤, (fun x => γ c (f x)) ∈ Q.comap W ⊓ IndF j₂ y₂ ⊤ := by
    intro c f hf
    exact hmem _ (h2 c _ (Submodule.mem_inf.1 hf).1)
  rcases hS (Q.comap W ⊓ IndF j₂ y₂ ⊤) inf_le_right st1 st2 with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    have hm := hmem (fun x => φ (e.symm x)) (by rw [hsurj]; exact hφ)
    rw [h] at hm
    have h0 := (Submodule.mem_bot ℂ).1 hm
    rw [← hsurj φ, h0, map_zero]
  · right
    refine le_antisymm hQ fun φ hφ => ?_
    have hm := hback hφ
    rw [← h] at hm
    have := (Submodule.mem_inf.1 hm).1
    rw [Submodule.mem_comap, hsurj] at this
    exact this

end Trans

section Base

variable {G H Γ Y : Type} [Group G] [Group H] [Group Γ] [AddCommGroup Y] [Module ℂ Y]
  [TopologicalSpace G] [IsTopologicalGroup G]

private theorem simpleBase [Subsingleton G] [Subsingleton H] (j : H →* G) (y : Representation ℂ (H × Γ) Y)
    (hy : y.IsIrreducible) : SimpleG (IndF j (y.comp (MonoidHom.inl H Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro Q hQ _ h2
  let ev : (G → Y) →ₗ[ℂ] Y := LinearMap.proj 1
  have hext : ∀ φ ψ : G → Y, φ 1 = ψ 1 → φ = ψ := by
    intro φ ψ h; funext x; rw [Subsingleton.elim x 1]; exact h
  have st : ∀ x, ∀ v ∈ Q.map ev, y x v ∈ Q.map ev := by
    rintro ⟨h, c⟩ v ⟨ψ, hψ, rfl⟩
    rw [Subsingleton.elim h 1]
    exact ⟨_, h2 c ψ hψ, rfl⟩
  rcases irrCases y hy (Q.map ev) st with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    have : φ 1 ∈ Q.map ev := ⟨φ, hφ, rfl⟩
    rw [h] at this
    exact hext _ _ ((Submodule.mem_bot ℂ).1 this)
  · right
    refine le_antisymm hQ fun φ hφ => ?_
    have : φ 1 ∈ Q.map ev := by rw [h]; trivial
    obtain ⟨ψ, hψ, e⟩ := this
    rwa [← hext ψ φ e]

end Base

section Prod

variable {A B H L Γ Y V : Type} [Group A] [Group B] [Group H] [Group L] [Group Γ] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup V] [Module ℂ V]

private def zAct (y : Representation ℂ (H × L) Y) : Representation ℂ (B × L) (B → Y) where
  toFun x := (rightReg ℂ B Y x.1) ∘ₗ (LinearMap.compLeft (y (1, x.2)) B)
  map_one' := by
    apply LinearMap.ext; intro φ; funext b
    show y (1, 1) (φ (b * 1)) = φ b
    have e : ((1, 1) : H × L) = 1 := rfl
    rw [e, map_one, mul_one]; rfl
  map_mul' a c := by
    apply LinearMap.ext; intro φ; funext b
    show y (1, a.2 * c.2) (φ (b * (a.1 * c.1))) = y (1, a.2) (y (1, c.2) (φ (b * a.1 * c.1)))
    have e : ((1 : H), a.2 * c.2) = (1, a.2) * (1, c.2) := by simp
    rw [e, map_mul, Module.End.mul_apply, mul_assoc]

variable [TopologicalSpace B] [IsTopologicalGroup B]

private theorem zStab (j : H →* B) (y : Representation ℂ (H × L) Y) (x : B × L) :
    ∀ φ ∈ IndF j (y.comp (MonoidHom.inl H L)) ⊤, zAct y x φ ∈ IndF j (y.comp (MonoidHom.inl H L)) ⊤ := by
  intro φ hφ
  refine indMk (fun h g => ?_) ?_
  · show y (1, x.2) (φ (j h * g * x.1)) = y (h, 1) (y (1, x.2) (φ (g * x.1)))
    have e : φ (j h * (g * x.1)) = y (h, 1) (φ (g * x.1)) := indLaw hφ h _
    rw [mul_assoc, e, commY]
  · have hc : Continuous fun g : B => x.1 * g * x.1⁻¹ := by fun_prop
    have hs : {g : B | rightReg ℂ B Y g φ = φ} ∈ nhds (x.1⁻¹ * 1 * x.1) := by
      have e : x.1⁻¹ * 1 * x.1 = 1 := by group
      rw [e]; exact indSm hφ
    have hc' : Continuous fun g : B => x.1⁻¹ * g * x.1 := by fun_prop
    refine Filter.mem_of_superset (hc'.continuousAt.preimage_mem_nhds hs) ?_
    intro g hg
    have hg' : ∀ b, φ (b * (x.1⁻¹ * g * x.1)) = φ b := fun b =>
      congrFun (show rightReg ℂ B Y (x.1⁻¹ * g * x.1) φ = φ from hg) b
    funext b
    show y (1, x.2) (φ (b * g * x.1)) = y (1, x.2) (φ (b * x.1))
    rw [show b * g * x.1 = (b * x.1) * (x.1⁻¹ * g * x.1) by group, hg']

private def zRep (j : H →* B) (y : Representation ℂ (H × L) Y) :
    Representation ℂ (B × L) (IndF j (y.comp (MonoidHom.inl H L)) ⊤) where
  toFun x := (zAct y x).restrict (zStab j y x)
  map_one' := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    show zAct y 1 φ.1 = φ.1
    rw [map_one]; rfl
  map_mul' a c := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    show zAct y (a * c) φ.1 = zAct y a (zAct y c φ.1)
    rw [map_mul]; rfl

private def swp (P : Type) [Group P] : P × (B × Γ) →* B × (P × Γ) where
  toFun x := (x.2.1, (x.1, x.2.2))
  map_one' := rfl
  map_mul' _ _ := rfl

private def y3 (P : Type) [Group P] (y : Representation ℂ (H × (P × Γ)) Y) : Representation ℂ (P × H) Y :=
  y.comp
    { toFun := fun x => (x.2, (x.1, 1))
      map_one' := rfl
      map_mul' := fun a b => by simp }

variable [TopologicalSpace A] [IsTopologicalGroup A] [TopologicalSpace H]

private theorem prodStep (P : Subgroup A) (j : H →* B) (hj : Topology.IsEmbedding j)
    (hsm : ∀ N ∈ nhds (1 : B), ∃ U : Subgroup B, IsOpen (U : Set B) ∧ (U : Set B) ⊆ N)
    (y : Representation ℂ (H × (P × Γ)) Y) (ρ : Representation ℂ P V) (f : V →ₗ[ℂ] Y) (hL : LocOk P ρ) (hf : f ≠ 0)
    (hfρ : ∀ p v, f (ρ p v) = y (1, (p, 1)) (f v)) (hopen : ∀ v, IsOpen {h : H | y (h, 1) v = v})
    (hIH : SimpleG (IndF j (y.comp (MonoidHom.inl H (P × Γ))) ⊤) fun c : P × Γ => y (1, c)) :
    SimpleG (IndF (MonoidHom.prodMap P.subtype j) (y3 P y) ⊤) fun c : Γ => y (1, (1, c)) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (LinearMap.ext hh)
  obtain ⟨U, F, hU, hF⟩ := indSeed j y (f v₀) hj hsm (hopen _)
  let Wf : Submodule ℂ V :=
    { carrier := {v | ∀ h, j h ∈ U → y (h, 1) (f v) = f v}
      add_mem' := by
        intro a b ha hb h hh
        rw [map_add, map_add, ha h hh, hb h hh]
      zero_mem' := by intro h _; simp
      smul_mem' := by
        intro c a ha h hh
        rw [map_smul, map_smul, ha h hh] }
  have hWst : ∀ p, ∀ v ∈ Wf, ρ p v ∈ Wf := by
    intro p v hv h hh
    rw [hfρ, commY, hv h hh]
  have hWtop : Wf = ⊤ := by
    rcases irrCases ρ hL.irr Wf hWst with e | e
    · exfalso
      have : v₀ ∈ Wf := fun h hh => hU h hh
      rw [e] at this
      exact hv₀ (by rw [(Submodule.mem_bot ℂ).1 this, map_zero])
    · exact e
  have hWv : ∀ v h, j h ∈ U → y (h, 1) (f v) = f v := by
    intro v
    have : v ∈ Wf := by rw [hWtop]; trivial
    exact this
  let Z := IndF j (y.comp (MonoidHom.inl H (P × Γ))) ⊤
  let fz : V →ₗ[ℂ] Z := LinearMap.codRestrict Z (F ∘ₗ f) fun v => (hF (f v) (hWv v)).1
  have hfza : ∀ v, (fz v : B → Y) = F (f v) := fun _ => rfl
  have hfz : fz ≠ 0 := by
    intro e
    apply hv₀
    have h1 := (hF (f v₀) (hWv v₀)).2.1
    rw [← h1, ← hfza, e]
    rfl
  let y₂ : Representation ℂ (P × (B × Γ)) Z := (zRep j y).comp (swp P)
  have hy₂a : ∀ (x : P × (B × Γ)) (ζ : Z) (b : B), (y₂ x ζ : B → Y) b = y (1, (x.1, x.2.2)) ((ζ : B → Y) (b * x.2.1)) :=
    fun _ _ _ => rfl
  have hZn : Nontrivial Z := by
    obtain ⟨v, hv⟩ : ∃ v, fz v ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hfz (LinearMap.ext hh)
    exact ⟨⟨_, _, hv⟩⟩
  have hy₂ : y₂.IsIrreducible := by
    refine irrOf y₂ hZn fun W hW => ?_
    have hQ : W.map Z.subtype ≤ Z := Submodule.map_subtype_le Z W
    have s1 : ∀ g, ∀ φ ∈ W.map Z.subtype, rightReg ℂ B Y g φ ∈ W.map Z.subtype := by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨_, hW (1, (g, 1)) w hw, ?_⟩
      funext b
      show y (1, (1, 1)) ((w : B → Y) (b * g)) = (w : B → Y) (b * g)
      have e : ((1, (1, 1)) : H × (P × Γ)) = 1 := rfl
      rw [e, map_one]; rfl
    have s2 : ∀ c : P × Γ, ∀ φ ∈ W.map Z.subtype, (fun x => y (1, c) (φ x)) ∈ W.map Z.subtype := by
      rintro c _ ⟨w, hw, rfl⟩
      refine ⟨_, hW (c.1, (1, c.2)) w hw, ?_⟩
      funext b
      show y (1, (c.1, c.2)) ((w : B → Y) (b * 1)) = y (1, c) ((w : B → Y) b)
      rw [mul_one]
    rcases hIH _ hQ s1 s2 with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
      have : (w : B → Y) ∈ W.map Z.subtype := ⟨w, hw, rfl⟩
      rw [h] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · right
      refine (Submodule.eq_top_iff').2 fun w => ?_
      have : (w : B → Y) ∈ W.map Z.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', e⟩ := this
      rwa [← Subtype.ext (a1 := w') (a2 := w) e]
  have hint : ∀ p v, fz (ρ p v) = y₂ (p, 1) (fz v) := by
    intro p v
    apply Subtype.ext
    funext b
    rw [hy₂a, hfza, hfza, hfρ]
    have e := (hF (f v) (hWv v)).2.2 (p, 1) b
    rw [e, show ((p, 1) : P × (B × Γ)).2.1 = (1 : B) from rfl, mul_one]
    rfl
  have hS := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indStep P ρ y₂ fz hL hy₂ hfz hint
  let Sp := IndF P.subtype (y₂.comp (MonoidHom.inl P (B × Γ))) ⊤
  let W' : (A → Z) →ₗ[ℂ] (A × B → Y) :=
    { toFun := fun Ψ x => (Ψ x.1 : B → Y) x.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : ∀ Ψ Ψ', W' Ψ = W' Ψ' → Ψ = Ψ' := by
    intro Ψ Ψ' e
    funext a
    apply Subtype.ext
    funext b
    exact congrFun e (a, b)
  have hcur : ∀ φ ∈ IndF (MonoidHom.prodMap P.subtype j) (y3 P y) ⊤, ∃ Ψ ∈ Sp, W' Ψ = φ := by
    intro φ hφ
    have hs : {g : A × B | rightReg ℂ (A × B) Y g φ = φ} ∈ nhds (((1 : A), (1 : B)) : A × B) := indSm hφ
    have hb : ∀ a, (fun b => φ (a, b)) ∈ Z := by
      intro a
      refine indMk (fun h g => ?_) ?_
      · have t := indLaw hφ ((1 : P), h) (a, g)
        have e : (MonoidHom.prodMap P.subtype j) ((1 : P), h) * (a, g) = (a, j h * g) := by simp
        rw [e] at t
        exact t
      · have hc : Continuous fun b : B => ((1 : A), b) := by fun_prop
        refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hs) ?_
        intro b hb
        funext x
        have t := congrFun (show rightReg ℂ (A × B) Y ((1 : A), b) φ = φ from hb) (a, x)
        have t' : φ ((a, x) * ((1 : A), b)) = φ (a, x) := t
        show φ (a, x * b) = φ (a, x)
        simpa using t'
    refine ⟨fun a => ⟨fun b => φ (a, b), hb a⟩, indMk (fun p a => ?_) ?_, rfl⟩
    · apply Subtype.ext
      funext b
      have t := indLaw hφ (p, (1 : H)) (a, b)
      have e : (MonoidHom.prodMap P.subtype j) (p, (1 : H)) * (a, b) = ((p : A) * a, b) := by simp
      rw [e] at t
      show φ ((p : A) * a, b) = y (1, (p, 1)) (φ (a, b * 1))
      rw [mul_one]
      exact t
    · have hc : Continuous fun a : A => (a, (1 : B)) := by fun_prop
      refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hs) ?_
      intro a' ha'
      funext a
      apply Subtype.ext
      funext b
      have t := congrFun (show rightReg ℂ (A × B) Y (a', (1 : B)) φ = φ from ha') (a, b)
      have t' : φ ((a, b) * (a', (1 : B))) = φ (a, b) := t
      show φ (a * a', b) = φ (a, b)
      simpa using t'
  intro Q hQ h1 h2
  have hback : ∀ Ψ, W' Ψ ∈ Q → Ψ ∈ Q.comap W' ⊓ Sp := by
    intro Ψ h
    obtain ⟨Ψ', h', e⟩ := hcur _ (hQ h)
    rw [← hinj _ _ e]
    exact Submodule.mem_inf.2 ⟨by rw [Submodule.mem_comap, e]; exact h, h'⟩
  have st1 : ∀ g, ∀ Ψ ∈ Q.comap W' ⊓ Sp, rightReg ℂ A Z g Ψ ∈ Q.comap W' ⊓ Sp := by
    intro g Ψ hΨ
    refine hback _ ?_
    have t := h1 (g, 1) _ (Submodule.mem_inf.1 hΨ).1
    have e : W' (rightReg ℂ A Z g Ψ) = rightReg ℂ (A × B) Y (g, 1) (W' Ψ) := by
      funext x
      show ((Ψ (x.1 * g) : Z) : B → Y) x.2 = ((Ψ (x * (g, 1)).1 : Z) : B → Y) (x * (g, 1)).2
      simp
    rw [e]
    exact t
  have st2 : ∀ c : B × Γ, ∀ Ψ ∈ Q.comap W' ⊓ Sp, (fun x => y₂ (1, c) (Ψ x)) ∈ Q.comap W' ⊓ Sp := by
    intro c Ψ hΨ
    refine hback _ ?_
    have t1 := h1 ((1 : A), c.1) _ (Submodule.mem_inf.1 hΨ).1
    have t2 := h2 c.2 _ t1
    have e : W' (fun x => y₂ (1, c) (Ψ x)) =
        fun x => y (1, (1, c.2)) (rightReg ℂ (A × B) Y ((1 : A), c.1) (W' Ψ) x) := by
      funext x
      show y (1, (1, c.2)) ((Ψ x.1 : B → Y) (x.2 * c.1)) =
        y (1, (1, c.2)) ((Ψ (x * ((1 : A), c.1)).1 : B → Y) (x * ((1 : A), c.1)).2)
      simp
    rw [e]
    exact t2
  rcases hS (Q.comap W' ⊓ Sp) inf_le_right st1 st2 with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    obtain ⟨Ψ, hΨ, e⟩ := hcur φ (hQ hφ)
    have hm : Ψ ∈ Q.comap W' ⊓ Sp := hback Ψ (by rw [e]; exact hφ)
    rw [h] at hm
    rw [← e, (Submodule.mem_bot ℂ).1 hm, map_zero]
  · right
    refine le_antisymm hQ fun φ hφ => ?_
    obtain ⟨Ψ, hΨ, e⟩ := hcur φ hφ
    have hm : Ψ ∈ Q.comap W' ⊓ Sp := by rw [h]; exact hΨ
    have := (Submodule.mem_inf.1 hm).1
    rw [Submodule.mem_comap, e] at this
    exact this

end Prod

section Fin

private def consG {r : ℕ} (G : Fin (r + 1) → Type) [∀ i, Group (G i)] : (∀ i, G i) ≃* G 0 × ∀ i : Fin r, G i.succ where
  toFun g := (g 0, fun i => g i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv g := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  right_inv x := by simp
  map_mul' _ _ := rfl

private theorem consSucc {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] (i : Fin r) (p : G i.succ) :
    consG G (Pi.mulSingle i.succ p) = (1, Pi.mulSingle i p) := by
  apply Prod.ext
  · exact Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i).symm p
  · funext k
    show Pi.mulSingle i.succ p k.succ = (Pi.mulSingle i p : ∀ j : Fin r, G j.succ) k
    by_cases h : k = i
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (fun e => h (Fin.succ_injective _ e)), Pi.mulSingle_eq_of_ne h]

private theorem consZero {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] (p : G 0) :
    consG G (Pi.mulSingle 0 p) = (p, 1) :=
  Prod.ext (Pi.mulSingle_eq_same 0 p) (funext fun k => Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero k) p)

private theorem consCont {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] :
    Continuous (consG G) :=
  (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)

private theorem consCont' {r : ℕ} {G : Fin (r + 1) → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] :
    Continuous (consG G).symm := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · exact continuous_fst
  · exact (continuous_apply k).comp continuous_snd

private theorem smallPi {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (h : ∀ i, ∀ N ∈ nhds (1 : G i), ∃ U : Subgroup (G i), IsOpen (U : Set (G i)) ∧ (U : Set (G i)) ⊆ N) :
    ∀ N ∈ nhds (1 : ∀ i, G i), ∃ U : Subgroup (∀ i, G i), IsOpen (U : Set (∀ i, G i)) ∧ (U : Set (∀ i, G i)) ⊆ N := by
  intro N hN
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  choose U hUo hUt using fun i => h i (t i) (ht i)
  refine ⟨Subgroup.pi Set.univ U, ?_, ?_⟩
  · have e : ((Subgroup.pi Set.univ U : Subgroup (∀ i, G i)) : Set (∀ i, G i)) = Set.univ.pi fun i => (U i : Set (G i)) := rfl
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun i _ => hUo i
  · intro x hx
    apply hsub
    intro i _
    exact hUt i (hx i (Set.mem_univ i))

end Fin

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indProdG :
    ∀ (r : ℕ) {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] (P : ∀ i, Subgroup (G i)) {Γ : Type} [Group Γ] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
      (y : Representation ℂ ((∀ i, P i) × Γ) Y), y.IsIrreducible → (∀ v, IsOpen {p : ∀ i, P i | y (p, 1) v = v}) →
      (∀ i, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i) V) (f : V →ₗ[ℂ] Y), LocOk (P i) ρ ∧ f ≠ 0 ∧
        ∀ p v, f (ρ p v) = y (Pi.mulSingle i p, 1) (f v)) →
      SimpleG (IndF (piIncl P) (y.comp (MonoidHom.inl _ Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro r
  induction r with
  | zero =>
    intro G _ _ _ P Γ _ Y _ _ y hy _ _
    exact simpleBase (piIncl P) y hy
  | succ r ih =>
    intro G _ _ _ P Γ _ Y _ _ y hy hsm hloc
    let eP := consG (fun i => P i)
    let θ : (∀ i : Fin r, P i.succ) × (P 0 × Γ) →* (∀ i, P i) × Γ :=
      { toFun := fun x => (eP.symm (x.2.1, x.1), x.2.2)
        map_one' := Prod.ext (map_one eP.symm) rfl
        map_mul' := fun a b => Prod.ext (map_mul eP.symm (a.2.1, a.1) (b.2.1, b.1)) rfl }
    let y' : Representation ℂ ((∀ i : Fin r, P i.succ) × (P 0 × Γ)) Y := y.comp θ
    have hsurj : ∀ x, ∃ z, θ z = x := by
      rintro ⟨p, c⟩
      refine ⟨((eP p).2, ((eP p).1, c)), Prod.ext ?_ rfl⟩
      exact eP.symm_apply_apply p
    obtain ⟨V, a1, a2, ρ, f, hL, hf, hfr⟩ := hloc 0
    have hYn : Nontrivial Y := by
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra hh
        push_neg at hh
        exact hf (LinearMap.ext hh)
      exact ⟨⟨_, _, hv⟩⟩
    have hy' : y'.IsIrreducible := by
      refine irrOf y' hYn fun W hW => irrCases y hy W fun x v hv => ?_
      obtain ⟨z, rfl⟩ := hsurj x
      exact hW z v hv
    have hsm' : ∀ v, IsOpen {p : ∀ i : Fin r, P i.succ | y' (p, 1) v = v} := by
      intro v
      have hc : Continuous fun p : (∀ i : Fin r, P i.succ) => eP.symm ((1 : P 0), p) :=
        consCont'.comp (by fun_prop)
      exact (hsm v).preimage hc
    have hloc' : ∀ i : Fin r, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i.succ) V) (f : V →ₗ[ℂ] Y),
        LocOk (P i.succ) ρ ∧ f ≠ 0 ∧ ∀ p v, f (ρ p v) = y' (Pi.mulSingle i p, 1) (f v) := by
      intro i
      obtain ⟨V, b1, b2, ρ, f, hL, hf, hfr⟩ := hloc i.succ
      refine ⟨V, b1, b2, ρ, f, hL, hf, fun p v => ?_⟩
      have e : eP.symm (1, Pi.mulSingle i p) = Pi.mulSingle i.succ p := by
        rw [MulEquiv.symm_apply_eq]
        exact (consSucc (G := fun i => P i) i p).symm
      rw [hfr]
      show y (Pi.mulSingle i.succ p, 1) (f v) = y (eP.symm (1, Pi.mulSingle i p), 1) (f v)
      rw [e]
    have hIH := ih (G := fun i : Fin r => G i.succ) (fun i => P i.succ) y' hy' hsm' hloc'
    have hB : ∀ N ∈ nhds (1 : ∀ i : Fin r, G i.succ), ∃ U : Subgroup (∀ i : Fin r, G i.succ),
        IsOpen (U : Set (∀ i : Fin r, G i.succ)) ∧ (U : Set (∀ i : Fin r, G i.succ)) ⊆ N := by
      refine smallPi fun i => ?_
      obtain ⟨V, b1, b2, ρ, f, hL, _, _⟩ := hloc i.succ
      exact hL.small
    have hemb : Topology.IsEmbedding (piIncl fun i : Fin r => P i.succ) :=
      Topology.IsEmbedding.piMap fun _ => Topology.IsEmbedding.subtypeVal
    have hfρ : ∀ p v, f (ρ p v) = y' (1, (p, 1)) (f v) := by
      intro p v
      have e : eP.symm (p, 1) = Pi.mulSingle 0 p := by
        rw [MulEquiv.symm_apply_eq]
        exact (consZero (G := fun i => P i) p).symm
      rw [hfr]
      show y (Pi.mulSingle 0 p, 1) (f v) = y (eP.symm (p, 1), 1) (f v)
      rw [e]
    have hfin := prodStep (P 0) (piIncl fun i : Fin r => P i.succ) hemb hB y' ρ f hL hf hfρ hsm' hIH
    have hγ : (fun c : Γ => y' (1, (1, c))) = fun c => y (1, c) := by
      funext c
      show y (eP.symm (1, 1), c) = y (1, c)
      rw [show eP.symm ((1 : P 0), (1 : ∀ i : Fin r, P i.succ)) = 1 from map_one eP.symm]
    rw [hγ] at hfin
    refine simpleTrans (consG G) consCont consCont' (piIncl P) _ eP (fun h => rfl) _ (y3 (P 0) y') (fun h => ?_) _ hfin
    show y (h, 1) = y (eP.symm (eP h), 1)
    rw [MulEquiv.symm_apply_apply]
