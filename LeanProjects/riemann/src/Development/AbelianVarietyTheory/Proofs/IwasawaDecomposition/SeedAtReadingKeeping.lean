import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeedChoices

set_option maxHeartbeats 1000000 in

theorem seed_at_reading_keeping : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face3 D A3) (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (ψ : AddChar (AF D.host.F) ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)), L.Is A3.A.μ0 → Seed.TupL A3 L mu twPl → Seed.RecL A3 L eG → Seed.LevelsL A3 L eG F.lv2 → Seed.ModY D → Seed.ModWAt D.what₂.embLL MW → Seed.VPos D → IsStdChar D ψ (-1) → ∀ Qb : ∀ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)), (∀ t, A3.A.fam.amb.FR t → Bridge.Gf D.sp.X' → cX.W) → (∀ i t, A3.A.fam.amb.FL i t → Bridge.Gf (Vc D i) → (cV i).W) → Prop, (∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m), ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL A3 L eG cX cV pl Sb B plI SF ∧ Qb cX cV (fun t φ => B.jR t φ) fun i t φ => B.jL i t φ) → ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.ψ = ψ ∧ R.MW = MW ∧ HEq R.eG eG ∧ R.mu = mu ∧ R.twPl = twPl ∧ Seed.PrIso R.MX R.cX R.prX ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧ Qb R.cX R.cV (fun t φ => R.B.jR t φ) fun i t φ => R.B.jL i t φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ F L eG mu twPl ψ MW hL hmu hrec hlev hY hMW hV hψ Qb hB
  obtain ⟨θ, hθ⟩ := Formalism.IndefR.Eqv.infFamExists_holds D
  obtain ⟨hMY, ⟨MX⟩⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb, hQ⟩ := hB θ hθ MX
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  have hMW' : Seed.ModWAt (D := D) (sg0 D A3.A) MW := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ htie.v0]; exact hMW
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, rfl,
    hPr, ?_, ?_, ?_, hb.sb, hQ⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW', hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

end GlobalTheory.SeedChoices
