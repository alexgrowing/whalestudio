import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMass
open scoped Classical

namespace GlobalTheory.PtFib

open MulAction GlobalTheory.MassConj

def ConjTgt (H : Type) [Group H] (_K : Subgroup H) : Type := H

variable {H X : Type} [Group H] [MulAction H X]

def ConjTgt.val {K : Subgroup H} (γ : ConjTgt H K) : H := γ

instance (K : Subgroup H) : MulAction K (ConjTgt H K) where
  smul k γ := ((k : H) * (show H from γ) * (k : H)⁻¹ : H)
  one_smul := by
    show ∀ γ : H, (1 : H) * γ * (1 : H)⁻¹ = γ
    intro γ; group
  mul_smul k l := by
    show ∀ γ : H, ((k : H) * l) * γ * ((k : H) * l)⁻¹ = (k : H) * ((l : H) * γ * (l : H)⁻¹) * (k : H)⁻¹
    intro γ; group

theorem mk_smul' {T α : Type} [Group T] [MulAction T α] (t : T) (x : α) :
    (Quotient.mk'' (t • x) : orbitRel.Quotient T α) = Quotient.mk'' x :=
  Quotient.sound' (mem_orbit x t)

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (q : orbitRel.Quotient T α) (x : α)
    (h : (Quotient.mk'' x : orbitRel.Quotient T α) = q) : ∃ t : T, t • x = Quotient.out q := by
  have h2 : (Quotient.mk'' (Quotient.out q) : orbitRel.Quotient T α) = Quotient.mk'' x := by
    rw [h]; exact Quotient.out_eq' q
  exact orbitRel_apply.1 (Quotient.eq''.1 h2)

end GlobalTheory.PtFib

namespace GlobalTheory.PtFib

open MulAction GlobalTheory.MassConj

variable {H X : Type} [Group H] [MulAction H X]

theorem card_stab_pair (x : X) (γ : H) :
    Nat.card (stabilizer (stabilizer H x) (show ConjTgt H (stabilizer H x) from γ)) =
      Nat.card (stabilizer H (ConjPair.mk γ x : ConjPair H X)) := by
  apply Nat.card_congr
  refine
   { toFun := fun k => ⟨((k : stabilizer H x) : H), ?_⟩
     invFun := fun d => ⟨⟨(d : H), ?_⟩, ?_⟩
     left_inv := fun k => rfl
     right_inv := fun d => rfl }
  · have hk : ((k : stabilizer H x) : H) * γ * ((k : stabilizer H x) : H)⁻¹ = γ := k.2
    rw [GlobalTheory.MassConj.mem_stabilizer_iff]
    refine ⟨?_, (k : stabilizer H x).2⟩
    calc ((k : stabilizer H x) : H) * γ
        = ((k : stabilizer H x) : H) * γ * ((k : stabilizer H x) : H)⁻¹ * ((k : stabilizer H x) : H) := by group
      _ = γ * ((k : stabilizer H x) : H) := by rw [hk]
  · exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).1 d.2).2
  · have hd := ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).1 d.2).1
    rw [MulAction.mem_stabilizer_iff]
    show (d : H) * γ * (d : H)⁻¹ = γ
    rw [hd]; group

theorem card_stab_smul (t : H) (p : ConjPair H X) :
    Nat.card (stabilizer H (t • p)) = Nat.card (stabilizer H p) :=
  (Nat.card_congr (stabilizerEquivStabilizer (rfl : t • p = t • p)).toEquiv).symm

theorem mk_out_pt (p : ConjPair H X) :
    (Quotient.mk'' (Quotient.out (Quotient.mk'' p : orbitRel.Quotient H (ConjPair H X))).pt :
      orbitRel.Quotient H X) = Quotient.mk'' p.pt := by
  obtain ⟨t, ht⟩ := exists_smul_eq_out' (Quotient.mk'' p : orbitRel.Quotient H (ConjPair H X)) p rfl
  rw [← ht, smul_pt, mk_smul']

theorem ptFib_mass (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ)
    (hf : ∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x)
    (hfin : ∀ x : X, Finite (MulAction.stabilizer H x))
    (hsupp : ∀ x : X, (Function.support fun γ : H => f γ x).Finite) (x : X) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  haveI := hfin x
  let K := stabilizer H x
  let F : ConjTgt H K → ℂ := fun γ => f γ x
  have hF : ∀ (k : K) (γ : ConjTgt H K), F (k • γ) = F γ := by
    intro k γ
    change H at γ
    show f ((k : H) * γ * (k : H)⁻¹) x = f γ x
    have h := hf k γ x
    rwa [show (k : H) • x = x from k.2] at h
  have key := GlobalTheory.finsum_orbits_stabilizer_mass F hF (hsupp x)
  let g : ConjTgt H K → {O : orbitRel.Quotient H (ConjPair H X) //
      (Quotient.mk'' (Quotient.out O).pt : orbitRel.Quotient H X) = Quotient.mk'' x} :=
    fun γ => ⟨Quotient.mk'' (ConjPair.mk (H := H) γ x), by rw [mk_out_pt]⟩
  have hg : ∀ a b : ConjTgt H K, a ∈ orbit K b → g a = g b := by
    rintro a b ⟨k, hk⟩
    apply Subtype.ext
    show (Quotient.mk'' (ConjPair.mk (H := H) a x) : orbitRel.Quotient H (ConjPair H X)) = Quotient.mk'' (ConjPair.mk (H := H) b x)
    have : (ConjPair.mk (H := H) a x : ConjPair H X) = (k : H) • ConjPair.mk (H := H) b x := by
      ext
      · rw [smul_elt, ← hk]; rfl
      · rw [smul_pt]; exact k.2.symm
    rw [this, mk_smul']
  let φ : orbitRel.Quotient K (ConjTgt H K) → {O : orbitRel.Quotient H (ConjPair H X) //
      (Quotient.mk'' (Quotient.out O).pt : orbitRel.Quotient H X) = Quotient.mk'' x} :=
    Quotient.lift g (fun a b hab => hg a b (orbitRel_apply.1 hab))
  have hφ : ∀ γ : ConjTgt H K, φ (Quotient.mk'' γ) = g γ := fun γ => rfl
  have hinj : Function.Injective φ := by
    intro o1 o2 h
    induction o1 using Quotient.inductionOn' with | h a => ?_
    induction o2 using Quotient.inductionOn' with | h b => ?_
    rw [hφ, hφ] at h
    have h1 : (Quotient.mk'' (ConjPair.mk (H := H) a x) : orbitRel.Quotient H (ConjPair H X)) =
        Quotient.mk'' (ConjPair.mk (H := H) b x) := congrArg Subtype.val h
    obtain ⟨δ, hδ⟩ := orbitRel_apply.1 (Quotient.eq''.1 h1)
    have he : δ * ConjTgt.val b * δ⁻¹ = ConjTgt.val a := congrArg ConjPair.elt hδ
    have hp : δ • x = x := congrArg ConjPair.pt hδ
    apply Quotient.sound'
    exact orbitRel_apply.2 ⟨⟨δ, hp⟩, he⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨O, hO⟩
    obtain ⟨t, ht⟩ := orbitRel_apply.1 (Quotient.eq''.1 hO)

    refine ⟨Quotient.mk'' (show ConjTgt H K from (t⁻¹ * (Quotient.out O).elt * t : H)), ?_⟩
    rw [hφ]
    apply Subtype.ext
    show (Quotient.mk'' (ConjPair.mk (t⁻¹ * (Quotient.out O).elt * t) x) :
      orbitRel.Quotient H (ConjPair H X)) = O
    have : (ConjPair.mk (t⁻¹ * (Quotient.out O).elt * t) x : ConjPair H X) = t⁻¹ • Quotient.out O := by
      ext
      · rw [smul_elt]; group
      · rw [smul_pt, ← ht, inv_smul_smul]
    rw [this, mk_smul']
    exact Quotient.out_eq' O
  let e := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  rw [← finsum_comp_equiv e]
  have hterm : ∀ o : orbitRel.Quotient K (ConjTgt H K),
      (1 / (Nat.card (stabilizer H (Quotient.out (e o).1)) : ℂ)) *
          f (Quotient.out (e o).1).elt (Quotient.out (e o).1).pt =
        ((Nat.card (stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) := by
    intro o
    have h1 : (e o).1 = Quotient.mk'' (ConjPair.mk (H := H) (Quotient.out o) x) := by
      show (φ o).1 = _
      conv_lhs => rw [← Quotient.out_eq' o]
      rfl
    rw [h1]
    obtain ⟨t, ht⟩ := exists_smul_eq_out'
      (Quotient.mk'' (ConjPair.mk (H := H) (Quotient.out o) x) : orbitRel.Quotient H (ConjPair H X)) _ rfl
    rw [← ht, card_stab_smul, smul_elt, smul_pt, hf, ← card_stab_pair, one_div]
    rfl
  rw [finsum_congr hterm, key, one_div]
  rfl

end GlobalTheory.PtFib
