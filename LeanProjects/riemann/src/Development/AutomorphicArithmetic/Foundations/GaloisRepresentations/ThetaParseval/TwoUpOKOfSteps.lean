import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtQIffRowQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP

open Sub

theorem twoUpOK_of_steps (hT : UpperTheory.TP.TLiftK) (hC : ChrPairs) (hU : UpOf) (hB : BaseNG) : TwoUpOK := by
  intro E _ _ _ hE hK _ hI n hn he U hA lam hl w₀ hw₀
  obtain ⟨Bs, δ, 𝔞, hG, hX, hW⟩ := hB E hE hI
  obtain ⟨d₀, hd⟩ := hT E Bs ⟨hG.cm, hK, hG.unram, hG.std, hG.inert, hG.psiP⟩ n hn _ rfl (hX n)
  set t := 2 * (d₀ + n) + 1 with ht
  obtain ⟨b, hb⟩ := (Set.finite_range fun x : InfinitePlace (maximalRealSubfield E) × Fin n => (lam (Bs.emb x.1).1).w x.2).bddBelow
  obtain ⟨κ, m, χX, χW, mX, mW, ψ, p, hκ, hj, hne, hu, hu'⟩ :=
    hC E hE n t he ⟨_, rfl⟩ Bs.emb (2 * b - ((n + t : ℕ) : ℤ)) w₀ hw₀
  have key : ∀ j, ∃ U' lam', IsUp U lam κ m U' lam' (ψ j) (p j) := fun j => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hj j
    obtain ⟨U', hL⟩ := hd (n + t) (by omega) _ δ rfl (hW (n + t)) (χX j) (χW j) (mX j) (mW j) a1 a2 a3 a4 a5 a6 U
      (fun w => lam (Bs.emb w).1) hA (fun w => hl _) fun w k => by
        have h1 := a7 w
        have h2 : b ≤ (lam (Bs.emb w).1).w k := hb ⟨(w, k), rfl⟩
        omega
    exact ⟨U', hU E n t hn (by omega) Bs _ _ _ _ U hA lam hl U' hL κ m _ _ a8⟩
  obtain ⟨U₁, l₁, h₁⟩ := key 0
  obtain ⟨U₂, l₂, h₂⟩ := key 1
  exact ⟨t, κ, m, U₁, U₂, l₁, l₂, ψ 0, ψ 1, p 0, p 1, he.add_odd ⟨_, rfl⟩, hκ, h₁, h₂, hne, hu, hu'⟩

theorem twoUpOK_of_k (h : UpperTheory.TP.TLiftK) : TwoUpOK := twoUpOK_of_steps h Chr.chrPairs_holds upOf baseNG

end UpperTheory.Gal.TP
