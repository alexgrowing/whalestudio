import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.MemAOfPow
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation

private def ZM {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Submodule ℤ_[l] (X.Fn l) where
  carrier := {a | ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (a u) = 0}
  add_mem' {a b} ha hb u := by
    show AdicCompletion.eval (idl l) (X.Kl l) n (a u + b u) = 0
    rw [map_add, ha u, hb u, add_zero]
  zero_mem' u := by
    show AdicCompletion.eval (idl l) (X.Kl l) n 0 = 0
    exact map_zero _
  smul_mem' c a ha u := by
    show AdicCompletion.eval (idl l) (X.Kl l) n (c • a u) = 0
    rw [map_smul, ha u, smul_zero]

private def Sm {l : ℕ} [Fact l.Prime] (n : ℕ) (x : Fin 2 → Qbar l) : Prop := ∀ i, ‖x i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

private theorem Sm.add {l : ℕ} [Fact l.Prime] {n : ℕ} {x y : Fin 2 → Qbar l} (hx : Sm n x) (hy : Sm n y) : Sm n (x + y) := by
  unfold Sm at *
  intro i
  rw [Pi.add_apply]
  exact (PadicAlgCl.isNonarchimedean l (x i) (y i)).trans (max_le (hx i) (hy i))

private theorem Sm.smul {l : ℕ} [Fact l.Prime] {n : ℕ} {x : Fin 2 → Qbar l} {k : Qbar l} (hk : ‖k‖ ≤ 1) (hx : Sm n x) :
    Sm n (k • x) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans (hx i)

private theorem Sm.sub {l : ℕ} [Fact l.Prime] {n : ℕ} {x y : Fin 2 → Qbar l} (hx : Sm n x) (hy : Sm n y) : Sm n (x - y) := by
  unfold Sm at *
  intro i
  rw [Pi.sub_apply, sub_eq_add_neg]
  refine (PadicAlgCl.isNonarchimedean l _ _).trans (max_le (hx i) ?_)
  rw [norm_neg]
  exact hy i

private theorem Sm.sum {l : ℕ} [Fact l.Prime] {n : ℕ} {T : Type} (S : Finset T) (x : T → Fin 2 → Qbar l) (h : ∀ t, Sm n (x t)) :
    Sm n (∑ t ∈ S, x t) := by
  induction S using Finset.induction_on with
  | empty => intro i; simp
  | insert a S ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] c.O).FG)
  have hB : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ ∑ g ∈ s, ‖(g : PadicAlgCl l)‖ := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := by
      rw [hs]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem g hg =>
      exact Finset.single_le_sum (f := fun g : c.O => ‖(g : PadicAlgCl l)‖)
        (fun _ _ => norm_nonneg _) hg
    | zero =>
      simp only [ZeroMemClass.coe_zero, norm_zero]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    | add x y _ _ hx hy =>
      rw [AddMemClass.coe_add]
      exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [SetLike.val_smul, Algebra.smul_def, norm_mul]
      have hr : ‖algebraMap ℤ_[l] (PadicAlgCl l) r‖ ≤ 1 := by
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
        exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one r)
      exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans hx
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ g ∈ s, ‖(g : PadicAlgCl l)‖) hlt
  have hle : ‖a ^ n‖ ≤ ∑ g ∈ s, ‖(g : PadicAlgCl l)‖ := hB ⟨a ^ n, c.O.pow_mem ha n⟩
  rw [norm_pow] at hle
  linarith

end UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation

open UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation in
theorem UpperTheory.V.Z.Kato.Nb.sN2rho :
    UpperTheory.V.Z.Kato.Nb.SN2rho := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hAdm he hmat
  obtain ⟨cp, hcp⟩ := UpperTheory.Kd.K4.pur ε X l N (2 * e - 1)
  refine ⟨cp + cL X l N (2 * e - 1), ?_⟩
  intro p _ hp hcop a δ ha hδ hab c₀ c₁ r n Y Y' z z' hR hR' hC
  obtain ⟨β, b1, hβ, hb1, hY⟩ := hR
  obtain ⟨β', b2, hβ', hb2, hY'⟩ := hR'
  obtain ⟨B0, hB0, hC⟩ := hC
  choose L hL using fun y => (hB0 y).2.2
  obtain ⟨_, _, _, _, hpr_add, hpr_smul, hprO, hprG, _⟩ := hAdm
  obtain ⟨hEqv, hAS, hSm, hSum, _, hAct, hGal, _⟩ := UpperTheory.V.Z.Kato.Nb.sApi Ω ε X l n
  have hStab := UpperTheory.V.Z.Kato.Nb.sBStab Ω ε X l N (2 * e - 1) (NeZero.pos N)
  set w := 2 * e - 1 with hw
  set cl := cL X l N w with hcl
  set i := inv1 (l ^ r) p with hi
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hpr_add
  have hPs : ∀ u v, pr (u - v) = pr u - pr v := fun u v => map_sub P u v
  have hPsum : ∀ {T : Type} (S : Finset T) (f : T → X.Fn l), pr (∑ t ∈ S, f t) = ∑ t ∈ S, pr (f t) :=
    fun S f => map_sum P f S
  have hPn : ∀ (k : ℕ) (v : X.Fn l), pr ((k : ℤ_[l]) • v) = (k : Qbar l) • pr v := by
    intro k v
    rw [hpr_smul]
    simp
  have hPl : ∀ (j : ℕ) (v : X.Fn l), pr ((l : ℤ_[l]) ^ j • v) = (l : Qbar l) ^ j • pr v := by
    intro j v
    rw [← Nat.cast_pow, hPn, Nat.cast_pow]
  have hPp : ∀ (j : ℕ) (v : X.Fn l), pr ((p : ℤ_[l]) ^ j • v) = (p : Qbar l) ^ j • pr v := by
    intro j v
    rw [← Nat.cast_pow, hPn, Nat.cast_pow]
  have hnO : ∀ k : ℕ, (k : Qbar l) ∈ cf.O := fun k => natCast_mem cf.O k
  have hTB : ∀ v ∈ X.B N l w, X.heckeT N l p v ∈ X.B N l w := fun v hv => (hStab v hv).2.2 p hp hcop
  have hDB : ∀ v ∈ X.B N l w, X.diam N l p v ∈ X.B N l w := by
    intro v hv
    exact (hStab v hv).2.1 _ (GlobalTheory.KZ.Betti.isDiam_sgD (NeZero.ne N) (Fact.out : l.Prime).ne_zero
      (Nat.Coprime.coprime_mul_left_right hcop)).1
  have hTc : ∀ u v, CgF X l n u v → CgF X l n (X.heckeT N l p u) (X.heckeT N l p v) := by
    intro u v h
    simp only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
    exact (hAS _ _ _ _ (hSum _ _ _ _ fun j _ => hAct _ _ _ h) (hAct _ _ _ h)).1
  have hDc : ∀ u v, CgF X l n u v → CgF X l n (X.diam N l p u) (X.diam N l p v) := by
    intro u v h
    exact hAct _ _ _ h
  have hCS : ∀ {u v : Fin 2 → Qbar l}, Cv n u v → Sm n (u - v) := fun h j => h j
  have hSC : ∀ {u v : Fin 2 → Qbar l}, Sm n (u - v) → Cv n u v := fun h j => h j
  let b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l := fun y =>
    ((l : Qbar l) ^ (cp + cl) * p) • ∑ t, b2 (t, y)
      - (l : Qbar l) ^ (cp + cl + c₁) • ((p : Qbar l) • b1 y - a • b1 (y * i)
        + ((p : Qbar l) ^ w * δ) • b1 (y * i ^ 2))
      + (l : Qbar l) ^ (cp + (c₀ + c₁)) • pr (L y)
  refine ⟨b, ?_, ?_⟩
  · intro y j
    simp only [b, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    refine add_mem (sub_mem (mul_mem (mul_mem (pow_mem (hnO l) _) (hnO p))
      (sum_mem fun t _ => hb2 _ _)) (mul_mem (pow_mem (hnO l) _) (add_mem (sub_mem
      (mul_mem (hnO p) (hb1 _ _)) (mul_mem ha (hb1 _ _))) (mul_mem (mul_mem (pow_mem (hnO p) _) hδ)
      (hb1 _ _))))) (mul_mem (pow_mem (hnO l) _) (hprO _ (hL y).1 j))
  intro s y
  have hb : ∀ y', β s y' ∈ X.B N l w := fun y' => (hβ s y').1
  have hβc : ∀ y', CgF X l n (β s y') ((l : ℤ_[l]) ^ c₀ • z s y') := fun y' => (hβ s y').2
  have hβ'c : ∀ t, CgF X l n (β' s (t, y)) ((l : ℤ_[l]) ^ (c₀ + c₁) • z' s (t, y)) := fun t => (hβ' s (t, y)).2
  have hLc : ∀ y', CgF X l n (L y') ((l : ℤ_[l]) ^ cl • B0 y') := fun y' => (hL y').2
  have hadd : ∀ {u v u' v' : X.Fn l}, CgF X l n u v → CgF X l n u' v' → CgF X l n (u + u') (v + v') :=
    fun h h' => (hAS _ _ _ _ h h').1
  have hsub : ∀ {u v u' v' : X.Fn l}, CgF X l n u v → CgF X l n u' v' → CgF X l n (u - u') (v - v') :=
    fun h h' => (hAS _ _ _ _ h h').2
  have hEB : (l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y) ∈ X.B N l w := by
    refine sub_mem (Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _
      (sum_mem fun t _ => (hβ' s (t, y)).1)) (Submodule.smul_mem _ _ (add_mem (sub_mem
      (Submodule.smul_mem _ _ (hb y)) (hTB _ (hb _))) (Submodule.smul_mem _ _ (hDB _ (hb _)))))))
      (Submodule.smul_mem _ _ (sub_mem ((hStab _ (hL _).1).1 s) (hL y).1))
  have hE1 : CgF X l n ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)) ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, (l : ℤ_[l]) ^ (c₀ + c₁) • z' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • (l : ℤ_[l]) ^ c₀ • z s y - X.heckeT N l p ((l : ℤ_[l]) ^ c₀ • z s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p ((l : ℤ_[l]) ^ c₀ • z s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s ((l : ℤ_[l]) ^ cl • B0 (y * (cycMod ℚ Ω l r s)⁻¹)) - (l : ℤ_[l]) ^ cl • B0 y)) :=
    hsub (hSm _ _ _ (hsub (hSm _ _ _ (hSum _ _ _ _ fun t _ => hβ'c t)) (hSm _ _ _ (hadd (hsub
      (hSm _ _ _ (hβc y)) (hTc _ _ (hβc _))) (hSm _ _ _ (hDc _ _ (hβc _)))))))
      (hSm _ _ _ (hsub (hGal _ _ _ (hLc _)) (hLc y)))
  have hCsy := hC s y
  beta_reduce at hCsy
  have hzero : ∀ {u v : X.Fn l}, CgF X l n u v → CgF X l n (u - v) 0 := by
    intro u v h
    have h' := hsub h (hEqv.refl v)
    rwa [sub_self] at h'
  have h1 := hzero hCsy
  have h2 := hSm ((l : ℤ_[l]) ^ (cl + (c₀ + c₁))) _ _ h1
  rw [smul_zero] at h2
  have hEz : CgF X l n ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)) 0 := by
    refine hEqv.trans hE1 ?_
    convert h2 using 2
    simp only [map_smul, ← Finset.smul_sum]
    module
  obtain ⟨E', hE'B, hEE'⟩ := hcp n _ hEB hEz
  have hsmall : Sm n (pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)))) := by
    rw [hEE', hPl]
    intro j
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (nle cf (hprO _ hE'B j))
  have hprE : pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y))) = (l : Qbar l) ^ cp • ((l : Qbar l) ^ cl • ((p : Qbar l) • ∑ t, pr (β' s (t, y)) - (l : Qbar l) ^ c₁ • ((p : Qbar l) • pr (β s y) - a • pr (β s (y * i)) + (p : Qbar l) ^ w • δ • pr (β s (y * i ^ 2)))) - (l : Qbar l) ^ (c₀ + c₁) • (rhoK W e ψ s *ᵥ pr (L (y * (cycMod ℚ Ω l r s)⁻¹)) - pr (L y))) := by
    simp only [hPl, hPs, hpr_add, hPsum, hPn, hPp]
    rw [(hab _ (hb _)).1, (hab _ (hb _)).2, hprG s _ (hL _).1]
  have hk : ∀ {k : Qbar l}, k ∈ cf.O → ‖k‖ ≤ 1 := fun hk => nle cf hk
  have hbig : Sm n (((l : Qbar l) ^ (cp + cl) * p) • ∑ t, (Y' s (t, y) - (pr (β' s (t, y)) + (rhoK W e ψ s *ᵥ b2 ((t, y) * kT l r p s) - b2 (t, y)))) - (l : Qbar l) ^ (cp + cl + c₁) • ((p : Qbar l) • (Y s (y) - (pr (β s (y)) + (rhoK W e ψ s *ᵥ b1 ((y) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y)))) - a • (Y s (y * i) - (pr (β s (y * i)) + (rhoK W e ψ s *ᵥ b1 ((y * i) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y * i)))) + ((p : Qbar l) ^ w * δ) • (Y s (y * i ^ 2) - (pr (β s (y * i ^ 2)) + (rhoK W e ψ s *ᵥ b1 ((y * i ^ 2) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y * i ^ 2))))) + pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)))) :=
    Sm.add (Sm.sub (Sm.smul (hk (mul_mem (pow_mem (hnO l) _) (hnO p)))
      (Sm.sum _ _ fun t => hCS (hY' s (t, y)))) (Sm.smul (hk (pow_mem (hnO l) _))
      (Sm.add (Sm.sub (Sm.smul (hk (hnO p)) (hCS (hY s y))) (Sm.smul (hk ha) (hCS (hY s _))))
      (Sm.smul (hk (mul_mem (pow_mem (hnO p) _) hδ)) (hCS (hY s _)))))) hsmall
  apply hSC
  convert hbig using 1
  rw [hprE]
  simp only [b]
  have hre : ∑ t, rhoK W e ψ s *ᵥ b2 ((t, y) * kT l r p s)
      = rhoK W e ψ s *ᵥ ∑ t, b2 (t, y * (cycMod ℚ Ω l r s)⁻¹) := by
    rw [← Matrix.mulVecLin_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.mulRight (cycM p s)⁻¹) _ _ (fun t => rfl)
  rw [show y * i * (cycMod ℚ Ω l r s)⁻¹ = y * (cycMod ℚ Ω l r s)⁻¹ * i from mul_right_comm _ _ _,
    show y * i ^ 2 * (cycMod ℚ Ω l r s)⁻¹ = y * (cycMod ℚ Ω l r s)⁻¹ * i ^ 2 from mul_right_comm _ _ _]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hre, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul]
  module
