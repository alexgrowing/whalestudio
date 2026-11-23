import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoOrderLOfCyclotomicIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicIrreducibleOfNotDvdDiscr

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.TameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Groups

variable {G Γ : Type} [Group G] [Group Γ]

def conjIn (H J : Subgroup G) (g : G) : Subgroup G where
  carrier := {x | x ∈ H ∧ g⁻¹ * x * g ∈ J}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have := J.mul_mem ha' hb'
    convert this using 1
    group
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have := J.inv_mem ha'
    convert this using 1
    group

def conjInEquiv (H J : Subgroup G) (g : G) : {γ : H // g⁻¹ * (γ : G) * g ∈ J} ≃ conjIn H J g where
  toFun γ := ⟨γ.1.1, γ.1.2, γ.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_conj (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G) (hrep : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := by
  obtain ⟨c, ⟨γ₀, k, hg⟩, -⟩ := hrep g
  haveI := hfin c
  let f : Bridge.stab ι J (y c) → {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := fun s =>
    ⟨⟨ι (γ₀ * s * γ₀⁻¹), γ₀ * s * γ₀⁻¹, rfl⟩, by
      have hs : (y c)⁻¹ * ι s * (y c) ∈ J := by
        have := s.2
        simpa [Bridge.stab, Subgroup.mem_comap, MulAut.conj_apply] using this
      have := J.mul_mem (J.mul_mem (J.inv_mem k.2) hs) k.2
      convert this using 1
      rw [hg]
      simp only [map_mul, map_inv]
      group⟩
  refine Finite.of_surjective f ?_
  rintro ⟨⟨_, a, rfl⟩, ha⟩
  refine ⟨⟨γ₀⁻¹ * a * γ₀, ?_⟩, ?_⟩
  · have := J.mul_mem (J.mul_mem k.2 ha) (J.inv_mem k.2)
    simp only [Bridge.stab, Subgroup.mem_comap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    convert this using 1
    rw [hg]
    simp only [map_mul, map_inv]
    group
  · apply Subtype.ext
    apply Subtype.ext
    show ι (γ₀ * (γ₀⁻¹ * a * γ₀) * γ₀⁻¹) = ι a
    congr 1
    group

end Groups

set_option maxHeartbeats 1600000 in

theorem rat_eq_one {D : D7} (V : TH.HSp D) (l : ℕ) (hl : l.Prime) (hN : V.rank + 1 < l)
    (hirr : Irreducible (Polynomial.cyclotomic l D.host.E)) (x : Bridge.Gf V) (hx : x ∈ (Bridge.ratF V).range)
    (hxl : x ^ l = 1) : x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  have hq := q.2
  simp only [Formalism.L2.Theta.GQ, GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map] at hq
  obtain ⟨u, -, hu⟩ := hq
  let φ : D.host.E →+* GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F))
  have key : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val = u.val.map φ := by
    have hu' : (q.1 : Formalism.L2.Theta.GA D V).1 =
        Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) u := hu.symm
    have h1 : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
        Formalism.UG.bc (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
          (q.1 : Formalism.L2.Theta.GA D V).1 := rfl
    rw [h1, hu']
    ext i j
    rfl
  rcases subsingleton_or_nontrivial (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) with hs | hs
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _
  · have hφ : Function.Injective φ := φ.injective
    have h2 := congrArg (fun z : Bridge.Gf V => (z : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val) hxl
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one] at h2
    rw [key] at h2
    have h3 : φ.mapMatrix (u.val ^ l) = φ.mapMatrix 1 := by
      rw [map_pow, map_one, RingHom.mapMatrix_apply]
      exact h2
    have hu1 : u.val ^ l = 1 := Matrix.map_injective hφ h3
    have hu2 : u.val = 1 :=
      GlobalTheory.no_order_l_of_cyclotomic_irreducible D.host.E l V.rank _ hl hirr hN hu1
    apply Subtype.ext
    apply Units.ext
    rw [key, hu2]
    have h4 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ = 1 := Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)
    rw [h4]
    rfl

theorem tameAt_of_smallAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hNr : P.Nr = (Vc D j).rank) (hS : SmallAt p j P w) :
    TameAt p j w := by
  obtain ⟨hl, hN, hd, -, -⟩ := hS
  intro g
  have hfin : Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} :=
    finite_conj (Bridge.ratF (Vc D j)) (levJ p j (p.R.mu w)) (p.R.B.L j (p.R.mu w)).pres.y (p.R.B.L j (p.R.mu w)).pres.reps
      (fun c => Finite.of_equiv _ ((p.R.B.L j (p.R.mu w)).pres.stabI c).toEquiv) g
  refine ⟨hfin, ?_⟩
  intro hdvd
  haveI : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hl⟩
  rw [Nat.card_congr (conjInEquiv _ _ g)] at hdvd
  haveI : Finite (conjIn (Bridge.ratF (Vc D j)).range (levJ p j (p.R.mu w)) g) := Finite.of_equiv _ (conjInEquiv _ _ g)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Formalism.EigenvalueLevelCeiling.plc w) hdvd
  have hirr := GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr D.host.E (Formalism.EigenvalueLevelCeiling.plc w) hl hd
  have hxl : (x : Bridge.Gf (Vc D j)) ^ (Formalism.EigenvalueLevelCeiling.plc w) = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
    rfl
  have h1 := rat_eq_one (Vc D j) (Formalism.EigenvalueLevelCeiling.plc w) hl (hNr ▸ hN) hirr x x.2.1 hxl
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact hl.one_lt.ne hx

theorem tameSt : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  unfold GlobalTheory.ExpTie.InRange GlobalTheory.BigOn.AtPts Formalism.MainNotions.Closed GlobalTheory.BigTop.EvPt
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ => ?_⟩⟩⟩
  intro j P W hD _ w _ _ hS
  exact tameAt_of_smallAt p j P w hD.Nr hS

end GlobalTheory.TameStab

end
