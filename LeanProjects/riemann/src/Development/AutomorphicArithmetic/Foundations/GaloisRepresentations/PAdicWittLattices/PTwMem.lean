import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
open GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh
universe u

private theorem sp_sub (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

private theorem pt_factor {Ω : Type} [Field Ω] {I : Type} [Finite I] {Y : Scheme.{0}}
    (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : I => Y)) : ∃ (c : I) (y₀ : UpperTheory.Gal.G3.sp Ω ⟶ Y), y₀ ≫ Sigma.ι (fun _ : I => Y) c = y := by
  haveI := sp_sub Ω
  let pt : UpperTheory.Gal.G3.sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
  obtain ⟨c, v, hv⟩ := (sigmaOpenCover (fun _ : I => Y)).exists_eq (y pt)
  have hι : (sigmaOpenCover (fun _ : I => Y)).f c = Sigma.ι (fun _ : I => Y) c := rfl
  rw [hι] at hv
  refine ⟨c, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) c) y ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨v, hv.trans (by rw [Subsingleton.elim w pt])⟩

private theorem pt_index {Ω : Type} [Field Ω] {I : Type} [Finite I] {Y : Scheme.{0}} {c d : I}
    (y z : UpperTheory.Gal.G3.sp Ω ⟶ Y) (h : y ≫ Sigma.ι (fun _ : I => Y) c = z ≫ Sigma.ι (fun _ : I => Y) d) : c = d := by
  let pt : UpperTheory.Gal.G3.sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
  have e : Sigma.ι (fun _ : I => Y) c (y pt) = Sigma.ι (fun _ : I => Y) d (z pt) := by
    have := congrArg (fun f : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : I => Y) => f pt) h
    simpa using this
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : I => Y) c d _ _).mp e)

theorem UpperTheory.Gal.G3.pTwMem :
    SplitsPts → PtsOfSplits → SigmaFEt → TwFEt → TwSplit → TwMem.{u} := by
  intro hS hP hSg hF hT B G _ X F _ T m i j a hmi hn I A _ _ e he r hr hu ht tr htr x
  have hij : X.K i ≤ X.K j := fun u hu' => by simpa using a.2 u hu'
  have b : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one (hmi.trans hij)
  have ar : ∀ y, X.admitted m i (r y) := fun y =>
    ⟨X.K_le j _ (hr y), fun u hu' => hmi (hn _ (hr y) u hu')⟩
  obtain ⟨hfin, het, -⟩ := hSg (X.tr i j 1 a.1 a.2) _ I (hF X i j a)
  have hsp := hT X m i j a b hmi hn A r ar hr hu
  let σ : I × A → (X.Z m ⟶ ∐ fun _ : I => X.Z i) := fun z =>
    X.tr m i (r z.2) (ar z.2).1 (ar z.2).2 ≫ Sigma.ι (fun _ : I => X.Z i) z.1
  have hσs : ∀ z, σ z ≫ (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) = X.tr m j 1 b.1 b.2 := by
    intro z
    simp only [σ, Category.assoc, Sigma.ι_desc]
    exact hsp.choose z.2
  have split : Splits (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) (X.tr m j 1 b.1 b.2) σ := by
    refine hS _ _ (I × A) σ hσs ?_
    intro Ω _ _ w y hy
    obtain ⟨c, y₀, rfl⟩ := pt_factor y
    have hy₀ : y₀ ≫ X.tr i j 1 a.1 a.2 = w ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hy, Category.assoc, Sigma.ι_desc]
    obtain ⟨d, hd, hd'⟩ := hP _ _ A _ hsp Ω w y₀ hy₀
    refine ⟨(c, d), ?_, ?_⟩
    · show w ≫ X.tr m i (r d) (ar d).1 (ar d).2 ≫ Sigma.ι (fun _ : I => X.Z i) c = _
      rw [← Category.assoc, hd]
    · rintro ⟨c', d'⟩ h
      have h' : (w ≫ X.tr m i (r d') (ar d').1 (ar d').2) ≫ Sigma.ι (fun _ : I => X.Z i) c' =
          y₀ ≫ Sigma.ι (fun _ : I => X.Z i) c := by
        rw [Category.assoc]; exact h
      obtain rfl : c' = c := pt_index _ _ h'
      have hm := (cancel_mono (Sigma.ι (fun _ : I => X.Z i) c')).mp h'
      rw [hd' d' hm]
  have hq : ∀ z, σ z ≫ (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) ≫ X.q j = X.q m := by
    intro z
    rw [← Category.assoc, hσs, X.tr_q]
  have key := htr (X.Z m) (X.q m) (X.tr m j 1 b.1 b.2) (X.tr_q ..) (I × A) σ hq split
    (T.pull _ ht x)
  rw [X.pl_eq T b, key, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
  have ad : X.admitted m j (e c * r y) := (ar y).mul (he c)
  have e1 : σ (c, y) ≫ (Sigma.desc fun c : I => X.tr i j (e c) (he c).1 (he c).2) =
      X.tr m j (e c * r y) ad.1 ad.2 := by
    simp only [σ, Category.assoc, Sigma.ι_desc]
    exact X.tr_mul m i j _ _ _ _ _ _ _ _
  rw [X.pl_eq T ad, ← T.pull_comp _ _ (hq (c, y)) ht (by rw [e1, X.tr_q])]
  simp only [e1]
