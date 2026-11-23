import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 G0' : Glob l L} (g : G.Hom G') (h : G.Hom G0) (g0 : G0.Hom G0')
  (h' : G'.Hom G0') (hc : ∀ a, h'.p₀ (g.p₀ a) = g0.p₀ (h.p₀ a)) {n : ℕ} {x : NP G0.frame n} (k : Kap x)
  (ρ' : G0'.G₀ →* GL (Fin n) x.A) (hρ : ∀ a, ρ' (g0.p₀ a) = x.ρ a)
  (κ' : Fin k.g → G0'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (g0.p₀ a) = k.κ j a)
  (X : Type) [CommRing X] [Algebra x.A X]

private theorem pull_inj {Z : Type} : Function.Injective fun (z : G'.G₀ → Z) (a : G.G₀) => z (g.p₀ a) :=
  fun _ _ e => funext fun b => by
    obtain ⟨a, rfl⟩ := g.p₀_surj b
    exact congrFun e a

include hc

private theorem rhoX_eq : (fun a => (x.desc g0 ρ' hρ).ρX X (h'.p₀ (g.p₀ a))) = fun a => x.ρX X (h.p₀ a) :=
  funext fun a => by rw [hc, NP.desc_ρX]

private theorem first_order_lift_comp_pullback :
    (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ (g.p₀ a))) = fun a => k.ρ1 X (h.p₀ a) :=
  funext fun a => by
    rw [hc]
    show (1 + DD.epM fun j => (κ' j (g0.p₀ (h.p₀ a))).map (algebraMap x.A X)) *
      (x.desc g0 ρ' hρ).ρX (DD X k.g) (g0.p₀ (h.p₀ a)) = _
    rw [NP.desc_ρX]
    simp only [hκ]
    rfl

private theorem selP_iff (z : G'.G₀ → Matrix (Fin n) (Fin n) X) :
    (fun a => z (g.p₀ a)) ∈ SelP h x X ↔ z ∈ SelP h' (x.desc g0 ρ' hρ) X := by
  have := g.sel_iff x.t (fun a => (x.desc g0 ρ' hρ).ρX X (h'.p₀ a)) (x.wX X) (x.wiX X) (Ev x.A X n x.a) z
  rw [rhoX_eq g h g0 h' hc ρ' hρ X] at this
  exact this

private theorem mem_selmer_first_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Sel1 h X k ↔ z ∈ Sel1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.sel_iff x.t (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (k.w1 X) (k.wi1 X) (W1 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem mem_selmer_second_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Sel2 h X k ↔ z ∈ Sel2 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.sel_iff x.t (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (k.w1 X) (k.wi1 X) (W2 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem mem_coboundary_first_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Bd1 h X k ↔ z ∈ Bd1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.bd_iff (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (W1 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem coboundary_first_eq_image_pullback :
    Bd1 h X k = (fun (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) (a : G.G₀) => z (g.p₀ a)) ''
      Bd1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨Y, -, -, e⟩ := id hz
    have e' : z = fun a => dY G'.frame (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) Y (g.p₀ a) := by
      funext a
      rw [e, ← g.dY_comp, first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X]
    refine ⟨_, (mem_coboundary_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).1 (e' ▸ hz), e'.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_coboundary_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).2 hz

private theorem pullback_selmer_first_subset :
    (fun (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) (a : G.G₀) => z (g.p₀ a)) ''
      Sel1 h' X (k.desc g0 ρ' hρ κ' hκ) ⊆ Sel1 h X k := by
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_selmer_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).2 hz

end

theorem UpperTheory.V.Pa.b_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (ρ' : Q.G0'.G₀ →* GL (Fin n) x.A) (hρ : ∀ a, ρ' (Q.g0.p₀ a) = x.ρ a) (κ' : Fin k.g → Q.G0'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (Q.g0.p₀ a) = k.κ j a) (D0 : ℕ), x.UnipOn T.H.toSubgroup → (T.B1 k D0 → Q.grp.B1 (k.desc Q.g0 ρ' hρ κ' hκ) D0) ∧ (T.B2 k → Q.grp.B2 (k.desc Q.g0 ρ' hρ κ' hκ)) := by
  intro l _ L G0 T Q n x k ρ' hρ κ' hκ D0 hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun m => (hC m).mono fun N hN => ?_⟩
    obtain ⟨hf, hle⟩ := hN
    have hs := pullback_selmer_first_subset (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m)
    have hb := coboundary_first_eq_image_pullback (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m)
    refine ⟨(hf.subset hs).of_finite_image (pull_inj (Q.gN N)).injOn, ?_⟩
    have h1 := Set.ncard_le_ncard hs hf
    rw [Set.ncard_image_of_injective _ (pull_inj (Q.gN N))] at h1
    rw [hb, Set.ncard_image_of_injective _ (pull_inj (Q.gN N))] at hle
    exact h1.trans hle
  · rintro ⟨C, hC⟩
    refine ⟨C, fun m => (hC m).mono fun N hN z hz => ?_⟩
    obtain ⟨c, hc, Ψ, hΨ, e⟩ := hN (fun i j a => z i j ((Q.gN N).p₀ a)) fun i j =>
      (selP_iff (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) ρ' hρ (x.Am m) _).2 (hz i j)
    haveI : T.H.toSubgroup.Normal := T.H.isNormal'
    obtain ⟨Ψ', rfl⟩ := (sel_desc l L (T.GN N) (Q.GN' N) G0 (Q.gN N) (T.h N) n x k T.H.toSubgroup m T.H.isOpen'
      (fun a ha => T.H_η a ha) hu (Q.kerN N)).2 Ψ (Or.inr hΨ)
    refine ⟨c, hc, Ψ', (mem_selmer_second_iff_pullback (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m) _).1 hΨ,
      fun j γ a b => ?_⟩
    obtain ⟨γ, rfl⟩ := (Q.gN N).p₀_surj γ
    exact e j γ a b
