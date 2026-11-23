import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCochainCupAssociativeOfPairing

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_cup_spec0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def t_aw_assoc0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M')
    (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w)
      (h3 : t + u = tu) (h4 : s + tu = w) a b c,
      ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
    ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
      (ab : Cochain ((chains R).obj E) M nm) (bc : Cochain ((chains R).obj E) M' mk)
      (x y : Cochain ((chains R).obj E) L w),
      μ.IsAW h1 α β ab → ν.IsAW h2 ab γ x → μ'.IsAW h3 β γ bc → ν'.IsAW h4 α bc y → x = y

theorem etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc (hs : t_cup_spec0) (ha : t_aw_assoc0) : EtaleCochainCupAssociativeOfPairing := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨ab, hab⟩ := (hs R μ (E := E) h1).1 α β
  rw [(hs R μ (E := E) h1).2 α β ab hab]
  obtain ⟨x, hx⟩ := (hs R ν (E := E) h2).1 ab γ
  rw [(hs R ν (E := E) h2).2 ab γ x hx]
  obtain ⟨bc, hbc⟩ := (hs R μ' (E := E) h3).1 β γ
  rw [(hs R μ' (E := E) h3).2 β γ bc hbc]
  obtain ⟨y, hy⟩ := (hs R ν' (E := E) h4).1 α bc
  rw [(hs R ν' (E := E) h4).2 α bc y hy]
  congr 1
  exact Subtype.ext (ha R μ ν μ' ν' hass E h1 h2 h3 h4 α.1 β.1 γ.1 ab.1 bc.1 x.1 y.1 hab hx hbc hy)

end LateralTheory.EtaleFoundations
