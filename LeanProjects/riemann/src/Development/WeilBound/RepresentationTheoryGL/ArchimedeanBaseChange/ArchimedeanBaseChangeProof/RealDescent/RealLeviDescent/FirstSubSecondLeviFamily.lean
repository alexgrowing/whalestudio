import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)

variable {n : ℕ}

theorem lr_strictAnti {lam : Fin n → ℤ} (hlam : Antitone lam) : StrictAnti (Lr lam) := by
  intro a b hab
  have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hlam hab.le
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Lr]
  linarith

section Intw

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : V →ₗ[ℂ] W)

def Intw (f : Module.End ℂ V) (g : Module.End ℂ W) : Prop := ∀ x, g (π x) = π (f x)

variable {π}

theorem Intw.add {f f' g g'} (h : Intw π f g) (h' : Intw π f' g') : Intw π (f + f') (g + g') := fun x => by
  simp [h x, h' x]

theorem Intw.sub {f f' g g'} (h : Intw π f g) (h' : Intw π f' g') : Intw π (f - f') (g - g') := fun x => by
  simp [h x, h' x]

theorem Intw.mul {f f' g g'} (h : Intw π f g) (h' : Intw π f' g') : Intw π (f * f') (g * g') := fun x => by
  simp [h' x, h (f' x)]

theorem Intw.smul {f g} (c : ℂ) (h : Intw π f g) : Intw π (c • f) (c • g) := fun x => by
  simp [h x]

theorem Intw.zero : Intw π (0 : Module.End ℂ V) 0 := fun x => by simp

theorem Intw.algebraMap (c : ℂ) : Intw π (algebraMap ℂ (Module.End ℂ V) c) (algebraMap ℂ (Module.End ℂ W) c) :=
  fun x => by simp [Module.algebraMap_end_apply]

theorem Intw.intCast (m : ℤ) : Intw π (m : Module.End ℂ V) (m : Module.End ℂ W) := by
  have := Intw.algebraMap (π := π) (m : ℂ)
  simpa using this

theorem Intw.sum {ι : Type*} (s : Finset ι) {f : ι → Module.End ℂ V} {g : ι → Module.End ℂ W}
    (h : ∀ i, Intw π (f i) (g i)) : Intw π (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Intw.zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact (h a).add ih

theorem Intw.listMap {ι : Type*} (l : List ι) {f : ι → Module.End ℂ V} {g : ι → Module.End ℂ W}
    (h : ∀ i, Intw π (f i) (g i)) : Intw π (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => simpa using Intw.algebraMap (π := π) 1
  | cons a l ih => simpa using (h a).mul ih

theorem Intw.ofFn {t : ℕ} {f : Fin t → Module.End ℂ V} {g : Fin t → Module.End ℂ W} (h : ∀ i, Intw π (f i) (g i)) :
    Intw π (List.ofFn f).prod (List.ofFn g).prod := by
  have := Intw.listMap (List.finRange t) h
  simpa [List.ofFn_eq_map] using this

theorem Intw.lift {X : Type} {G : X → Module.End ℂ V} {G' : X → Module.End ℂ W} (h : ∀ p, Intw π (G p) (G' p))
    (z : FreeAlgebra ℂ X) : Intw π (FreeAlgebra.lift ℂ G z) (FreeAlgebra.lift ℂ G' z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => simpa using Intw.algebraMap (π := π) r
  | grade1 p => simpa using h p
  | mul a b ha hb => simpa using ha.mul hb
  | add a b ha hb => simpa using ha.add hb

theorem Intw.qminor {F : Fin n → Fin n → Module.End ℂ V} {G : Fin n → Fin n → Module.End ℂ W}
    (h : ∀ a b, Intw π (F a b) (G a b)) {t : ℕ} (r c : Fin t → Fin n) (u : ℂ) :
    Intw π (Formalism.REAL.qminor F r c u) (Formalism.REAL.qminor G r c u) := by
  unfold Formalism.REAL.qminor
  refine Intw.sum _ fun σ => (Intw.intCast _).mul (Intw.ofFn fun k => ?_)
  unfold Formalism.REAL.Tm
  refine Intw.add ?_ (h _ _)
  split_ifs
  · exact Intw.algebraMap _
  · exact Intw.zero

theorem Intw.capS {F : Fin n → Fin n → Module.End ℂ V} {G : Fin n → Fin n → Module.End ℂ W}
    (h : ∀ a b, Intw π (F a b) (G a b)) (lev : Fin n → ℕ) (j : ℕ) (u : ℂ) : Intw π (capS F lev j u) (capS G lev j u) :=
  Intw.qminor h _ _ _

theorem Intw.algHom {X : Type} (φ : FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ V) (ψ : FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ W)
    (h : ∀ p, Intw π (φ (FreeAlgebra.ι ℂ p)) (ψ (FreeAlgebra.ι ℂ p))) (z : FreeAlgebra ℂ X) : Intw π (φ z) (ψ z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => simpa using Intw.algebraMap (π := π) r
  | grade1 p => exact h p
  | mul a b ha hb => simpa using ha.mul hb
  | add a b ha hb => simpa using ha.add hb

theorem Intw.eq {f f' : Module.End ℂ V} {g g' : Module.End ℂ W} (h : Intw π f g) (h' : Intw π f' g')
    (hs : Function.Surjective π) (e : f = f') : g = g' :=
  LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := hs y
    rw [h, h', e]

end Intw

def qOp {V : Type} [AddCommGroup V] [Module ℂ V] (B : Submodule ℂ V) (f : Module.End ℂ V) : Module.End ℂ (V ⧸ B) :=
  open Classical in if h : B ≤ B.comap f then B.mapQ B f h else 0

theorem qOp_intw {V : Type} [AddCommGroup V] [Module ℂ V] (B : Submodule ℂ V) (f : Module.End ℂ V)
    (h : ∀ x ∈ B, f x ∈ B) : Intw B.mkQ f (qOp B f) := fun x => by
  unfold qOp
  rw [dif_pos (show B ≤ B.comap f from fun y hy => h y hy)]
  rfl

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem first_add_second_levi_family (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    firstLeviFamily lev E1 E2 p q + secondLeviFamily lev E1 E2 p q = evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) := by
  simp only [firstLeviFamily, secondLeviFamily]
  module

theorem first_sub_second_levi_family (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    firstLeviFamily lev E1 E2 p q - secondLeviFamily lev E1 E2 p q = evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)) := by
  simp only [firstLeviFamily, secondLeviFamily]
  module

theorem fc_stab (hLS : LevStab) {lev : Fin n → ℕ} (hmono : Monotone lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hp : IsPairA E1 E2) (p q : Fin n) :
    (∀ x ∈ bdSub lev E1 E2, firstLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2) ∧
      ∀ x ∈ bdSub lev E1 E2, secondLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2 := by
  by_cases h : lev p = lev q
  · exact ⟨fun x hx => (hLS n lev hmono V E1 E2 hp p q h x hx).1, fun x hx => (hLS n lev hmono V E1 E2 hp p q h x hx).2⟩
  · have h1 : firstLeviFamily lev E1 E2 p q = 0 := by simp [firstLeviFamily, evLc, h]
    have h2 : secondLeviFamily lev E1 E2 p q = 0 := by simp [secondLeviFamily, evLc, h]
    exact ⟨fun x _ => by simp [h1], fun x _ => by simp [h2]⟩

end Chains

theorem multiplicity_assembly_holds : MultiplicityAssembly := by
  intro hP hI hH hA hLS hLR hSC hCC h4 h5
  intro n lam hlam lev hlev V _ _ E1 E2 hadm v w hv hw hv0 hx
  have hp : IsPairA E1 E2 := ⟨hadm.gl1, hadm.gl2, hadm.comm⟩
  obtain ⟨a, ha, hav⟩ := hP n lam lev V E1 E2 hadm _ v w hv hw hv0 hx
  obtain ⟨b, hb, hcong⟩ := hH n lev hlev.1 a ha
  obtain ⟨σ1, σ2, hsh, hcap⟩ := hCC n lam hlam lev hlev
  let B : Submodule ℂ (Cq n V) := bdSub lev E1 E2
  let FrobeniusMapsXPow : Fin n → Fin n → Module.End ℂ (Cq n V ⧸ B) := fun p q => qOp B (firstLeviFamily lev E1 E2 p q)
  let FiniteCocycleOfIntegral : Fin n → Fin n → Module.End ℂ (Cq n V ⧸ B) := fun p q => qOp B (secondLeviFamily lev E1 E2 p q)
  have i1 : ∀ p q, Intw B.mkQ (firstLeviFamily lev E1 E2 p q) (FrobeniusMapsXPow p q) := fun p q =>
    qOp_intw B _ (fc_stab hLS hlev.1 hp p q).1
  have i2 : ∀ p q, Intw B.mkQ (secondLeviFamily lev E1 E2 p q) (FiniteCocycleOfIntegral p q) := fun p q =>
    qOp_intw B _ (fc_stab hLS hlev.1 hp p q).2
  have hsurj : Function.Surjective B.mkQ := B.mkQ_surjective
  have hLq : IsLevPairA lev FrobeniusMapsXPow FiniteCocycleOfIntegral := by
    intro p q r s h1 h2
    obtain ⟨r1, r2, r3⟩ := hLR n lev hlev.1 V E1 E2 hp p q r s h1 h2
    have ite1 : ∀ (c : Prop) [Decidable c] (x y : Fin n),
        Intw B.mkQ (if c then firstLeviFamily lev E1 E2 x y else 0) (if c then FrobeniusMapsXPow x y else 0) := fun c _ x y => by
      split_ifs
      · exact i1 x y
      · exact Intw.zero
    have ite2 : ∀ (c : Prop) [Decidable c] (x y : Fin n),
        Intw B.mkQ (if c then secondLeviFamily lev E1 E2 x y else 0) (if c then FiniteCocycleOfIntegral x y else 0) := fun c _ x y => by
      split_ifs
      · exact i2 x y
      · exact Intw.zero
    exact ⟨Intw.eq (((i1 p q).mul (i1 r s)).sub ((i1 r s).mul (i1 p q))) ((ite1 _ p s).sub (ite1 _ r q)) hsurj r1,
      Intw.eq (((i2 p q).mul (i2 r s)).sub ((i2 r s).mul (i2 p q))) ((ite2 _ p s).sub (ite2 _ r q)) hsurj r2,
      Intw.eq ((i1 p q).mul (i2 r s)) ((i2 r s).mul (i1 p q)) hsurj r3⟩
  let ν : Fin n → ℝ := fun a => muQ lam lev a + 2 * rhoU lev a
  have hcent : ∀ a c, lev a = lev c → ν a = ν c := by
    intro a c h
    simp only [ν, muQ, rhoU, h, hlev.2 a c h]
  let c : Cq n V ⧸ B := B.mkQ (Pi.single (omU lev) v : Cq n V)
  have hsemi : ∀ a' c', lev a' = lev c' → (FrobeniusMapsXPow a' c' + FiniteCocycleOfIntegral a' c') c = if a' = c' then (ν a' : ℂ) • c else 0 := by
    intro a' c' h
    rw [((i1 a' c').add (i2 a' c')) _, hSC n lam hlam lev hlev V E1 E2 hadm v hv a' c' h]
    split_ifs <;> simp [c, ν]
  have hcap1 : ∀ u : ℂ, capProd FrobeniusMapsXPow lev σ1 u c = (∏ a, (u + (Lr lam a : ℂ))) • c := by
    intro u
    have hi := Intw.listMap (π := B.mkQ) (levs lev) (fun j => Intw.capS i1 lev j (u - σ1 j))
    simp only [capProd, c]
    rw [hi, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hcap V E1 E2 hadm v hv u).1
  have hcap2 : ∀ u : ℂ, capProd FiniteCocycleOfIntegral lev σ2 u c = (∏ a, (u + (Lr lam a : ℂ))) • c := by
    intro u
    have hi := Intw.listMap (π := B.mkQ) (levs lev) (fun j => Intw.capS i2 lev j (u - σ2 j))
    simp only [capProd, c]
    rw [hi, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hcap V E1 E2 hadm v hv u).2
  have hS5 := h5 n (Lr lam) (lr_strictAnti hlam) lev hlev.1 ν σ1 σ2 hsh (Cq n V ⧸ B) FrobeniusMapsXPow FiniteCocycleOfIntegral hLq c hsemi hcap1 hcap2
  obtain ⟨z, hz⟩ := h4 n lev hlev.1 b hb ν hcent
  let sc : ℕ × ℂ → ℂ := fun p => ∏ a ∈ blk lev p.1, (p.2 + σ1 p.1 + (Lr lam a : ℂ))
  have hev : ∀ z : FreeAlgebra ℂ (ℕ × ℂ), evCap lev FrobeniusMapsXPow z c = FreeAlgebra.lift ℂ sc z • c := by
    intro z
    induction z using FreeAlgebra.induction with
    | grade0 r => simp [Module.algebraMap_end_apply]
    | grade1 p => simp [evCap, sc, hS5 p.1 p.2]
    | mul x y hx hy => rw [map_mul, map_mul, Module.End.mul_apply, hy, map_smul, hx, smul_smul, mul_comm]
    | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, add_smul]
  have hkill : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0 := by
    intro l hl _
    have hlt : l.2.1.1 < l.2.1.2 := l.2.2
    simp only [xL, hl, Bool.false_eq_true, if_false]
    exact hv.2 _ _ hlt rfl
  obtain ⟨y, hyS, hyD, hyEq⟩ := hA n lev hlev.1 a b ha hcong V E1 E2 hp v hkill
  have iL : Intw B.mkQ (evLc lev E1 E2 b) (evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral b) := by
    refine Intw.algHom _ _ (fun p => ?_) b
    obtain ⟨s, p1, p2⟩ := p
    by_cases h : lev p1 = lev p2
    · cases s
      · have e : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (false, p1, p2)) = FrobeniusMapsXPow p1 p2 + FiniteCocycleOfIntegral p1 p2 := by
          simp [evLv, h, kA]
        rw [e, ← first_add_second_levi_family]
        exact (i1 p1 p2).add (i2 p1 p2)
      · have e : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (true, p1, p2)) = FrobeniusMapsXPow p1 p2 - FiniteCocycleOfIntegral p1 p2 := by
          simp [evLv, h, pA]
        rw [e, ← first_sub_second_levi_family]
        exact (i1 p1 p2).sub (i2 p1 p2)
    · have e1 : evLc lev E1 E2 (FreeAlgebra.ι ℂ (s, p1, p2)) = 0 := by simp [evLc, h]
      have e2 : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (s, p1, p2)) = 0 := by simp [evLv, h]
      rw [e1, e2]
      exact Intw.zero
  have hbd : bdL (inUU lev) E1 E2 y ∈ B := Submodule.mem_map.2 ⟨y, ⟨hyS, hyD⟩, rfl⟩
  have hcw : B.mkQ (Pi.single (omU lev) w : Cq n V) = FreeAlgebra.lift ℂ sc z • c := by
    have e1 : B.mkQ (Pi.single (omU lev) (evKP E1 E2 a v) - evLc lev E1 E2 b (Pi.single (omU lev) v) : Cq n V) = 0 := by
      rw [hyEq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hbd
    rw [map_sub, sub_eq_zero, ← iL] at e1
    rw [← hav, e1, hz (Cq n V ⧸ B) FrobeniusMapsXPow FiniteCocycleOfIntegral hLq c hsemi, hev z]
  refine ⟨FreeAlgebra.lift ℂ sc z, ?_⟩
  have hmem : w - FreeAlgebra.lift ℂ sc z • v ∈ hwSp E1 E2 (muQ lam lev) := sub_mem hw (Submodule.smul_mem _ _ hv)
  have hzero : (Pi.single (omU lev) (w - FreeAlgebra.lift ℂ sc z • v) : Cq n V) ∈ B := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, Pi.single_sub, Pi.single_smul, map_sub, map_smul, hcw]
    simp [c]
  obtain ⟨y', ⟨hy'S, hy'D⟩, hy'⟩ := Submodule.mem_map.1 hzero
  exact sub_eq_zero.1 (hI n lam hlam lev hlev V E1 E2 hadm _ y' hmem hy'S hy'D hy')

end PositivityTheory.RgBcC.RealD
