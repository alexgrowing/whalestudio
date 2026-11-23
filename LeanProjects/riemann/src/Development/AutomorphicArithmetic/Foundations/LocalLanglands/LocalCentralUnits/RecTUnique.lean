import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem par_of_laws {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (w.adicCompletion E) → WD h} (L : LawsT a ha rc) {y : IrrGL (w.adicCompletion E)}
    (hc : y.IsCusp) (hG : Good y) (hd : DZ y) : Par a y (rc y) where
  irr := L.cusp y hc
  dim := L.dim y
  tame := L.depth y hG hd
  central ω hω := L.central y ω hG hω
  type := (typeIff E Ω A w h rc).1 L.type y

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.recTUnique :
    UpperTheory.Zero.LLC.RecTUnique := by
  rintro E Ω _ _ _ _ _ A w h rc rc' ⟨a, ha, L⟩ ⟨a', ha', L'⟩ x hx
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain rfl : a' = a := (artEx E Ω A w h).unique ha' ha
  have key : ∀ y : IrrGL (w.adicCompletion E), y.IsCusp → GoodCusp y → rc y = rc' y := by
    intro y hc hg
    rcases id hg with h1 | ⟨⟨g, hgp, i, hi⟩, y₀, χ, hχ, hdz, rfl⟩
    · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ y).2.2.2.2.1 h1).2
      rw [L.one, L'.one]
    · haveI := hgp
      have ht := (clBasic _ y₀).2.1 χ hχ
      have hc₀ : y₀.IsCusp := ht.2.1.1 hc
      have hG : Good y₀ := ((goodSeg _).2.1 y₀ hc₀).2 (ht.2.2.1.1 hg)
      have e : rc' y₀ = rc y₀ :=
        (parUniq E Ω A w h _ ha g i hi y₀ hc₀ hdz (rc y₀) (par_of_laws L hc₀ hG hdz)).1 (rc' y₀)
          (par_of_laws L' hc₀ hG hdz)
      rw [L.twist _ _ _ hG, L'.twist _ _ _ hG, e, L.one, L'.one]
  obtain ⟨m, hm⟩ := Pr.exh _ x
  have hm' : IsL ((m.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
  rw [L.langlands _ x hm', L'.langlands _ x hm']
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [key Δ.first Δ.isCusp_first (((goodSeg _).1 _ x hm').1 hx Δ hΔ)]
