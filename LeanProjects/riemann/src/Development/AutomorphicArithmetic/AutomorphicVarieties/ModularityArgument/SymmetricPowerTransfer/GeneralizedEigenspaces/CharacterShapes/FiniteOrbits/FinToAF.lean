import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem core {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (Fi In Rt U : Subgroup G) [hN : Fi.Normal] (c : G →* H) (R : Representation ℂ H V)
    (hdec : ∀ x : G, ∃ f ∈ Fi, ∃ k ∈ In, x = f * k)
    (hcomm : ∀ f ∈ Fi, ∀ k ∈ In, Commute f k)
    (hint : ∀ x ∈ Fi, x ∈ In → x = 1)
    (hc : ∀ x ∈ Fi, c x = 1)
    (hU : U ≤ Fi)
    (Φ : Fi → V)
    (hL : ∀ (f : Fi), ∀ k ∈ In, (f : G) * k ∈ Rt → ∀ g, Φ (f * g) = R (c k) (Φ g))
    (hV : ∀ u : Fi, (u : G) ∈ U → ∀ g, Φ (g * u) = Φ g) :
    ∃ φ : G → V, (∀ γ ∈ Rt, ∀ g, φ (γ * g) = φ g) ∧ (∀ x ∈ In, ∀ g, φ (g * x) = R (c x⁻¹) (φ g)) ∧
      (∀ u ∈ U, ∀ g, φ (g * u) = φ g) ∧ (∀ g : Fi, φ g = Φ g) ∧
      ∀ (x : Fi) (cc : ℂ), UpperTheory.V.AlgebraTools.FinOrb U U (x : G) →
        dcF (U.subgroupOf Fi) x Φ = cc • Φ → dcF U (x : G) φ = cc • φ := by
  classical
  have hex : ∀ x : G, ∃ f : Fi, (f : G)⁻¹ * x ∈ In := by
    intro x
    obtain ⟨f, hf, k, hk, rfl⟩ := hdec x
    exact ⟨⟨f, hf⟩, by simpa using hk⟩
  choose p hp using hex
  have hpu : ∀ (f : Fi) (k : G), k ∈ In → p ((f : G) * k) = f := by
    intro f k hk
    have h2 : ((p ((f : G) * k) : G)⁻¹ * f) ∈ In := by
      have := In.mul_mem (hp ((f : G) * k)) (In.inv_mem hk)
      simpa [mul_assoc] using this
    have h3 : ((p ((f : G) * k) : G)⁻¹ * f) ∈ Fi := Fi.mul_mem (Fi.inv_mem (p _).2) f.2
    exact Subtype.ext (inv_mul_eq_one.mp (hint _ h3 h2))
  have hfac : ∀ g : G, ∃ k ∈ In, g = (p g : G) * k := fun g => ⟨_, hp g, by simp⟩
  have hmulR : ∀ (g : G) (f : Fi), p (g * f) = p g * f := by
    intro g f
    obtain ⟨k, hk, hg⟩ := hfac g
    have : g * f = ((p g * f : Fi) : G) * k := by
      have h := (hcomm f f.2 k hk).eq
      calc g * f = (p g : G) * (k * f) := by rw [← mul_assoc, ← hg]
        _ = _ := by rw [← h]; simp [mul_assoc]
    rw [this, hpu _ _ hk]
  have hmulL : ∀ (f : Fi) (g : G), p ((f : G) * g) = f * p g := by
    intro f g
    obtain ⟨k, hk, hg⟩ := hfac g
    have : (f : G) * g = ((f * p g : Fi) : G) * k := by
      calc (f : G) * g = (f : G) * ((p g : G) * k) := by rw [← hg]
        _ = _ := by simp [mul_assoc]
    rw [this, hpu _ _ hk]
  have hmulIn : ∀ (g k : G), k ∈ In → p (g * k) = p g := by
    intro g k hk
    obtain ⟨k', hk', hg⟩ := hfac g
    have : g * k = (p g : G) * (k' * k) := by
      calc g * k = (p g : G) * k' * k := by rw [← hg]
        _ = _ := by rw [mul_assoc]
    rw [this, hpu _ _ (In.mul_mem hk' hk)]
  have hinL : ∀ (k g : G), k ∈ In → p (k * g) = p g := by
    intro k g hk
    obtain ⟨k', hk', hg⟩ := hfac g
    have : k * g = (p g : G) * (k * k') := by
      have h := (hcomm (p g) (p g).2 k hk).eq
      calc k * g = k * ((p g : G) * k') := by rw [← hg]
        _ = _ := by rw [← mul_assoc, ← h, mul_assoc]
    rw [this, hpu _ _ (In.mul_mem hk hk')]
  refine ⟨fun x => R (c x)⁻¹ (Φ (p x)), ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ g
    have hk := hp γ
    have hγ' : (p γ : G) * ((p γ : G)⁻¹ * γ) = γ := by simp
    have hcγ : c ((p γ : G)⁻¹ * γ) = c γ := by
      rw [map_mul, map_inv, hc _ (p γ).2]; simp
    have hpp : p (γ * g) = p γ * p g := by
      have : γ * g = (p γ : G) * (((p γ : G)⁻¹ * γ) * g) := by simp [mul_assoc]
      rw [this, hmulL, hinL _ _ hk]
    have h := hL (p γ) _ hk (by rw [hγ']; exact hγ) (p g)
    simp only [hpp, h, hcγ, map_mul, mul_inv_rev, Module.End.mul_apply]
    rw [← Module.End.mul_apply (R (c γ)⁻¹), ← map_mul]
    simp
  · intro x hx g
    simp only [hmulIn g x hx, map_mul, mul_inv_rev, map_inv, Module.End.mul_apply]
  · intro u hu g
    have h := hmulR g ⟨u, hU hu⟩
    simp only at h
    simp only [h, map_mul, hc u (hU hu), mul_one]
    rw [hV ⟨u, hU hu⟩ hu]
  · intro g
    have h := hpu g 1 In.one_mem
    rw [mul_one] at h
    simp [h, hc _ g.2]
  · intro x cc hfo heig
    obtain ⟨hfo', hDC, -, Rr, hR1, hR2, hR3⟩ := dcSub G V Fi U x hfo
      (fun u hu => ⟨1, U.one_mem, by simp, by simpa using hU hu, by simpa using hU hu⟩) hN
    have hΦ : ∀ u ∈ U.subgroupOf Fi, ∀ g, Φ (g * u) = Φ g := fun u hu g => hV u hu g
    have hsum := (dcBasic Fi V (U.subgroupOf Fi) x hfo' Φ hΦ).2.2.2.2 Rr hR1 hR2
    have hφ : ∀ u ∈ U, ∀ g, (fun x => R (c x)⁻¹ (Φ (p x))) (g * u) = (fun x => R (c x)⁻¹ (Φ (p x))) g := by
      intro u hu g
      have h := hmulR g ⟨u, hU hu⟩
      simp only at h
      simp only [h, map_mul, hc u (hU hu), mul_one]
      rw [hV ⟨u, hU hu⟩ hu]
    have hsum' := (dcBasic G V U x hfo (fun x => R (c x)⁻¹ (Φ (p x))) hφ).2.2.2.2 (Rr.map (Function.Embedding.subtype _))
      (by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hy
        exact (hDC r).1 (hR1 r hr))
      (by
        intro y hy
        obtain ⟨r, ⟨hr, hry⟩, hu⟩ := hR3 y hy
        refine ⟨r, ⟨Finset.mem_map.mpr ⟨r, hr, rfl⟩, hry⟩, ?_⟩
        rintro r' ⟨hr', hry'⟩
        obtain ⟨r'', hr'', rfl⟩ := Finset.mem_map.mp hr'
        simpa using congrArg Subtype.val (hu r'' ⟨hr'', hry'⟩))
    funext g
    rw [hsum' g, Finset.sum_map]
    have hE := congrFun heig (p g)
    rw [hsum (p g)] at hE
    simp only [Function.Embedding.subtype_apply, Pi.smul_apply]
    have : ∀ r : Fi, R (c (g * r))⁻¹ (Φ (p (g * r))) = R (c g)⁻¹ (Φ (p g * r)) := by
      intro r
      rw [hmulR, map_mul, hc _ r.2, mul_one]
    simp only [this]
    rw [← map_sum, hE, Pi.smul_apply, map_smul]

theorem UpperTheory.V.Z.Sym.So.finToAF :
    UpperTheory.V.Z.Sym.So.FinToAF := by
  intro L _ _ _ n V _ _ R U hU Φ hL hV
  obtain ⟨-, -, hdec, hcomm, hext, hmem, -, -⟩ := uaFacts L n
  have hN : (finU L n).Normal := ⟨fun x hx g => (hmem _).1.2 fun τ => by
    simp [((hmem x).1.1 hx) τ]⟩
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := core (finU L n) (infU L n) (ratU L n) U (infC L n) R hdec hcomm
    (fun x hx hx' => hext x 1 (fun w => by simpa using (hmem x).2.1 hx' w)
      (fun τ => by simpa using (hmem x).1.1 hx τ))
    (fun x hx => by
      funext v
      exact (hmem x).1.1 hx v.embedding)
    hU Φ hL hV
  exact ⟨φ, ⟨h1, h2, h3⟩, h4, h5⟩

end
