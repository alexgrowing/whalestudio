import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.IntOfNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HeightLeOfDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtOfSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CompDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ChevPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.TanBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RegDom
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DomMin
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redAbs : UpperTheory.V.J.RedAbs := by
  intro l _ c _ F C₀ n hF hn S M Gd hAG hDB hTan ξ hξ hTI b hb
  haveI hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  haveI hq : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨x, L, Q, hO⟩ := UpperTheory.V.J.locAt l c F C₀ n hF hn S ξ hξ
  have hN : Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) :=
    UpperTheory.V.J.htUp l c F C₀ n hF hn S M hAG (fun Z hZ hMZ => (hDB Z hZ hMZ).1) _ x L Q hO hTI
  have hass := (UpperTheory.V.J.htLow l c F C₀ n hF hn S _ x L Q hO).2 hN
  have hTIle : ∀ P : Ideal S.A, P ≤ RingHom.ker ξ → S.u.TI P := fun P hle =>
    ⟨⟨fun h => hTI.1.1 (h.trans hle), fun h => hTI.1.2 (h.trans hle)⟩, fun h3 h => hTI.2 h3 (h.trans hle)⟩
  have hmin : ∀ P ∈ minimalPrimes S.A, P ≤ RingHom.ker ξ → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
    intro P hP hPq
    have hPp : P.IsPrime := hP.1.1
    have hPT := hTIle P hPq
    have hZp : (S.π P).IsPrime := Ideal.IsPrime.comap _
    have hMZ : M ≤ S.π P := hAG P hPp hPT
    obtain ⟨hle, hdn⟩ := hDB (S.π P) hZp hMZ
    have hdim : ringKrullDim (S.B ⧸ S.π P) = ((1 + n * F.d : ℕ) : WithBot ℕ∞) :=
      le_antisymm hle (UpperTheory.V.J.compDim l c F C₀ n hF hn S _ x L Q hO hTI P hP hPq)
    obtain ⟨ξ', hV, hT', hPk, hG⟩ := UpperTheory.V.J.genPt l c F C₀ n hF hn S P Gd hP hPT (hdn hdim)
    haveI hq' : (RingHom.ker ξ').IsPrime := RingHom.ker_isPrime _
    have hMk : M ≤ RingHom.ker (ξ'.comp S.inc) := fun m hm => hPk (hMZ hm)
    have hF1 := hTan ξ' hV hT' hMk hG
    have hrk : Module.rank (Qbar l) (PtDer ξ' (Qbar l)) ≤ ((n * F.d + 1 : ℕ) : Cardinal) := by
      refine (UpperTheory.V.J.tanBound l c F C₀ n hF hn S ξ' hV.1).trans ?_
      rw [Nat.cast_add, Nat.cast_one]
      gcongr
    obtain ⟨x', L', Q', hO'⟩ := UpperTheory.V.J.locAt l c F C₀ n hF hn S ξ' hV.1
    have hht := (UpperTheory.V.J.htLow l c F C₀ n hF hn S _ x' L' Q' hO').1
    have hdom := UpperTheory.V.J.regDom l c S.A ξ' (n * F.d + 1) hrk hht
    exact UpperTheory.V.J.domMin S.A (RingHom.ker ξ') hdom P hP hPk
  obtain ⟨s, hs, hsb⟩ := UpperTheory.V.J.redCrit S.A (RingHom.ker ξ) hq hass hmin (S.inc b)
    (fun P hPp hPq => hAG P hPp (hTIle P hPq) hb)
  exact ⟨s, fun h => hs (RingHom.mem_ker.2 h), hsb⟩
