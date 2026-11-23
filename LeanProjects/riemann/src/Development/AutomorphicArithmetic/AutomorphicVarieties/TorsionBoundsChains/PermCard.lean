import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.OrbStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CardStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermEmpty
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permCard :
    ∀ (G : Type) [Group G] (s j A : ℕ) (X : Type) [MulAction G X], OrbLe G X A → StabLe G X s →
      1 ≤ s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (A * s ^ (j + 1))) := by
  intro G _ s j A
  have hempty : ∀ (A : ℕ) (X : Type) [MulAction G X] [IsEmpty X], 1 ≤ s →
      CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (A * s ^ (j + 1))) := by
    intro A X _ _ hs
    obtain ⟨h1, h2⟩ := permEmpty G X (j + 1)
    exact ⟨h1, h2.trans (Nat.one_le_pow _ _ hs)⟩
  induction A with
  | zero =>
    intro X _ hO _ hs
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨hf, hc⟩ := hO
      haveI : Nonempty (MulAction.orbitRel.Quotient G X) := ⟨Quotient.mk'' x⟩
      have := Nat.card_pos (α := MulAction.orbitRel.Quotient G X)
      omega⟩
    exact hempty 0 X hs
  | succ A ih =>
    intro X _ hO hS hs
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact hempty _ X hs
    · obtain ⟨U, V, hUV, hne, htr, hSU, hSV, hOV⟩ := orbStep G X A s x hO hS
      obtain ⟨f, g, hf, hfg, hg⟩ := permSplit G X U V hUV
      obtain ⟨⟨u, v, huv⟩, -⟩ := les G _ _ _ f g hf hfg hg (j + 1)
      have h1 := permTrans G U s j hSU
      have h2 := ih V hOV hSV hs
      have h3 := cardStep _ _ _ u v _ _ huv h1 h2
      have e : s ^ (s ^ (j + 1)) * s ^ (A * s ^ (j + 1)) = s ^ ((A + 1) * s ^ (j + 1)) := by
        rw [← pow_add]; congr 1; ring
      rwa [e] at h3
