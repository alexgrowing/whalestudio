import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Faceexact

open UpperTheory.V UpperTheory.V.Af.BA UpperTheory.V.KT Pointwise in
theorem UpperTheory.bddFix_of_bounded_complex :
    UpperTheory.V.Af.BA.BddCx → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.ActRe → UpperTheory.V.Af.BA.SpanRe → UpperTheory.V.Af.BA.OrbRe → UpperTheory.V.Af.BA.MinStab → UpperTheory.V.Af.BA.BddFix := by
  intro hB hGood hAct hSpan hOrb hMin L _ _ _ N σ hσ
  obtain ⟨x, hx1, hx2⟩ := hAct L N σ hσ
  letI := x
  obtain ⟨hFC, hS0, hA⟩ := UpperTheory.V.ConeExtensionAcyclic.acyc_simp (hGood L N σ hσ)
  let K : Cx (Fix N σ) (UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) :=
    { S := UpperTheory.V.ConeExtensionAcyclic.simp (qr L N) (Tr L N)
      comp := fun f t ht => by
        obtain ⟨z, hz, hzt⟩ := ht
        exact ⟨z, hz, fun j => hzt (f j)⟩
      smul := fun g t ht => hx2 _ g t ht }
  refine hB _ _ K (fun m => UpperTheory.V.KT.faceexact _ _ hFC hS0 hA m) ?_ ?_
  · intro p
    obtain ⟨R, hRf, hR⟩ := hOrb L N σ hσ p
    refine ⟨{t : K.Tup p | (fun j => (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N)) ∈ R}, ?_, ?_⟩
    · refine hRf.preimage ?_
      intro a _ b _ hab
      apply Subtype.ext
      funext j
      exact Subtype.ext (Subtype.ext (congrFun hab j))
    · intro t
      obtain ⟨g, hg, hgR⟩ := hR t.1 t.2
      refine ⟨⟨g, hg⟩, ?_⟩
      have hfun : (fun j => ((((⟨g, hg⟩ : Fix N σ) • t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N))
          = fun j => g • (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N) :=
        funext fun j => hx1 _ _
      show (fun j => ((((⟨g, hg⟩ : Fix N σ) • t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N)) ∈ R
      rw [hfun]
      exact hgR
  · intro t
    set v : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N) := t.1 0 with hv
    set hh : UpperTheory.V.KT.HS L N := ((v : HR L N) : UpperTheory.V.KT.HS L N) with hhh
    have hRy : hh ∈ UpperTheory.V.KT.Ry L N := by
      intro y hy
      exact v.2.1 ⟨y, hy⟩
    have hsp := hSpan L N σ hσ 0 t.1 t.2
    have hmv : UpperTheory.V.KT.minVec hh = {y | ∀ j : Fin (0 + 1), UpperTheory.V.KT.q (((t.1 j : UpperTheory.V.ConeExtensionAcyclic.Vert (qr L N)) : HR L N) : UpperTheory.V.KT.HS L N) y = 1} := by
      ext y
      constructor
      · intro hy j
        have hj : j = 0 := Fin.ext (by omega)
        rw [hj]
        exact hy
      · intro hy
        exact hy 0
    have hsp' : UpperTheory.V.KT.Spans (UpperTheory.V.KT.minVec hh) := by
      rw [hmv]
      exact hsp
    haveI := hMin L N hh hRy hsp'
    refine Finite.of_injective
      (β := MulAction.stabilizer (UpperTheory.V.KT.Gm L N) (UpperTheory.V.KT.minVec hh))
      (fun g => ⟨((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N), ?_⟩) ?_
    · have hgt : (g.1 : Fix N σ) • t = t := g.2
      have hgv : (g.1 : Fix N σ) • v = v := congrArg (fun s : K.Tup 0 => s.1 0) hgt
      have hgh : ((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N) • hh = hh := by
        rw [hhh, ← hx1, hgv]
      rw [MulAction.mem_stabilizer_iff]
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show UpperTheory.V.KT.q hh (((g.1 : Fix N σ) : UpperTheory.V.KT.Gm L N)⁻¹ • z) = 1 ↔ UpperTheory.V.KT.q hh z = 1
      rw [← UpperTheory.V.KT.q_smul, hgh]
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext hab')
