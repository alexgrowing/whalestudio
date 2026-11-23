import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.TorsRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.CobOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixLev

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem unrInj_smul {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ∈ KStar.TotallyRealRoots.princ l 1) {x : QZ l}
    (hx : (l : ℤ_[l]) • x = 0) : (u : ℤ_[l]) • x = x := by
  obtain ⟨ι, hinj, hrange, hsmul⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  have hmem : x ∈ Set.range ι := (hrange x).2 (by simpa using hx)
  obtain ⟨a, rfl⟩ := hmem
  have hu' : PadicInt.toZModPow 1 (u : ℤ_[l]) = 1 := by
    have h := hu
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker] at h
    exact congrArg Units.val h
  rw [← hsmul, hu', one_mul]

set_option maxHeartbeats 400000 in

theorem UpperTheory.V.Odd.unrInj :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ f : Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]) → UnrHom (Fn E Ω l 1) Ω l, Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ D e
  classical
  obtain ⟨ι, hinj, hrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  let eq1 := ZMod.ringEquivCongr (pow_one l)
  haveI hcyc := (UpperTheory.V.Kum.fnCyc E Ω l 1).1
  have hgal : galOf E (Fn E Ω l 1) Ω = levU l (galOf E E Ω) 1 :=
    UpperTheory.V.Kum.galOfCyc E Ω l 1 E (Fn E Ω l 1)
  have key : ∀ z : Z1 (qzTw D e), (∀ g, (l : ℤ_[l]) • (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) g = 0) →
      ∃ φ : UnrHom (Fn E Ω l 1) Ω l, ∀ σ,
        ι (eq1.symm (φ.1 σ)) = (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ)) := by
    intro z hz
    have hzc : Continuous (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) := z.2.1
    have hzco : ∀ g h, (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (g * h) = (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) g + (qzTw D e g) ((z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) h) := z.2.2
    let w : G (Fn E Ω l 1) Ω → QZ l := fun σ => (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ))
    have hwt : ∀ σ, w σ ∈ Set.range ι := fun σ => (hrange _).2 (by simpa using hz _)
    let φ : G (Fn E Ω l 1) Ω → ZMod l := fun σ => eq1 (Function.invFun ι (w σ))
    have hφ : ∀ σ, ι (eq1.symm (φ σ)) = w σ := by
      intro σ
      simp only [φ, RingEquiv.symm_apply_apply]
      exact Function.invFun_eq (hwt σ)
    have hdet : ∀ σ (c : ZMod l), ι (eq1.symm c) = w σ → φ σ = c := by
      intro σ c h
      have h2 := hφ σ
      rw [← h] at h2
      have h3 := hinj h2
      simpa using congrArg eq1 h3
    have hmul : ∀ a b, w (a * b) = w a + w b := by
      intro a b
      have hg := hzco (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω a)) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω b))
      have h1 : (qzTw D e) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω a)) = qzG E Ω l e (galEmb E (Fn E Ω l 1) Ω a) := by
        rw [← qzTw_comp_toGS D e]
        rfl
      have hm := galEmb_mem E (Fn E Ω l 1) Ω a
      rw [hgal] at hm
      have hu : (cycZ E Ω l (galEmb E (Fn E Ω l 1) Ω a)) ^ (-e) ∈ KStar.TotallyRealRoots.princ l 1 :=
        Subgroup.zpow_mem (KStar.TotallyRealRoots.princ l 1) (Subgroup.mem_comap.1 hm.2) _
      rw [h1, qzG_apply, unrInj_smul hu (by simpa using hz _), ← map_mul, ← map_mul] at hg
      exact hg
    have hz1 : (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) 1 = 0 := by
      have h := hzco 1 1
      rw [map_one, mul_one, Module.End.one_apply] at h
      simpa using h
    have hwc : Continuous w :=
      hzc.comp ((continuous_toGS Ω _).comp (galEmbTop E (Fn E Ω l 1) Ω).1.continuous)
    refine ⟨⟨φ, ?_, ?_, ?_⟩, hφ⟩
    · exact ((IsLocallyConstant.iff_continuous w).2 hwc).comp (fun y => eq1 (Function.invFun ι y))
    · intro a b
      apply hdet
      rw [map_add, map_add, hφ, hφ, hmul]
    · intro A hA g hg
      have hg' : galEmb E (Fn E Ω l 1) Ω g ∈ Ine A := by
        have h := ((galEmbFam E (Fn E Ω l 1) Ω l).1 A).2
        rw [← h] at hg
        exact hg
      have h1 : toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω g) = 1 := by
        by_cases htop : A = ⊤
        · have h := ((places E Ω l A).2.1 htop).1
          rw [h, Subgroup.mem_bot] at hg'
          rw [hg', map_one]
        · obtain ⟨v, hv⟩ := (places E Ω l A).1 htop
          rw [toGS, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          apply Subgroup.le_topologicalClosure
          apply Subgroup.subset_normalClosure
          have hvS : v ∈ (↑D.S : Set (HeightOneSpectrum (𝓞 E)))ᶜ := by
            intro h
            rw [D.hS] at h
            exact hA (((places E Ω l A).2.2.1 v hv).2 h)
          exact Set.mem_iUnion₂.2 ⟨v, hvS, Set.mem_iUnion₂.2 ⟨A, hv, hg'⟩⟩
      apply hdet
      simp only [w, h1, hz1, map_zero]
  choose zf hzf using fun x : Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]) =>
    UpperTheory.V.Odd.torsRep E Ω l D e x.1 ((Submodule.mem_torsionBy_iff _ _).1 x.2)
  choose φf hφf using fun x => key (zf x) (hzf x).2
  refine ⟨φf, ?_⟩
  intro x y hxy
  have hv : ∀ σ, (zf x : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ)) =
      (zf y : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ)) := by
    intro σ
    rw [← hφf x σ, ← hφf y σ, hxy]
  apply Subtype.ext
  rw [(hzf x).1, (hzf y).1, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply UpperTheory.V.Odd.cobOne E Ω l D e
  intro g hg
  rw [← range_galEmb E (Fn E Ω l 1) Ω] at hg
  obtain ⟨σ, rfl⟩ := hg
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [hv σ, sub_self]
